use std::{alloc::Layout, path::Path, sync::Arc};

use vm_memory::GuestMemoryMmap;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset},
    aligner::Aligner,
    elf_loader::{self, LoadedElf, MemoryManager},
    translation_table::{Aarch64TranslationGranule, TranslationTableManager},
    HvMemoryFlags,
};
use anyhow::{anyhow, Context};
use log::{debug, trace};
use vm_memory::GuestMemory;

#[derive(Debug, Clone, Copy)]
pub struct DramConfig {
    pub start_va: GuestVaAddress,
    pub size: u64,
}

#[derive(Debug)]
pub struct GuestMemoryManager {
    translation_table_mgr: TranslationTableManager,
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    memory: Arc<GuestMemoryMmap>,
    dram_ipa_start: GuestIpaAddress,
    dram_va_start: GuestVaAddress,
    memory_size: usize,
    used_ipa: Offset,
    used_va: Offset,
    dram_config: Option<DramConfig>,
}

impl GuestMemoryManager {
    pub fn new(
        va_start: GuestVaAddress,
        ipa_start: GuestIpaAddress,
        size: usize,
    ) -> anyhow::Result<Self> {
        let memory = Arc::new(
            GuestMemoryMmap::from_ranges(&[(ipa_start.as_guest_address(), size)])
                .context("error allocating guest memory")?,
        );

        let granule = Aarch64TranslationGranule::P16k;
        let txsz = 28;
        let tmp_ttmgr =
            TranslationTableManager::new(granule, txsz, GuestIpaAddress(0), GuestIpaAddress(0))?;

        let mut mm = Self {
            translation_table_mgr: tmp_ttmgr,
            memory,
            dram_ipa_start: ipa_start,
            dram_va_start: va_start,
            memory_size: size,
            used_ipa: Offset(0),
            used_va: Offset(0),
            // This is temporary
            ttbr0: GuestIpaAddress(0),
            ttbr1: GuestIpaAddress(0),
            dram_config: None,
        };

        let ttbr_layout = mm.translation_table_mgr.get_top_ttbr_layout()?;

        let (_, ttbr0) = mm.allocate_ipa(ttbr_layout, format_args!("TTBR0"))?;
        let (_, ttbr1) = mm.allocate_ipa(ttbr_layout, format_args!("TTBR1"))?;
        mm.translation_table_mgr = TranslationTableManager::new(granule, txsz, ttbr0, ttbr1)?;
        mm.ttbr0 = ttbr0;
        mm.ttbr1 = ttbr1;

        Ok(mm)
    }

    pub fn get_ttbr_0(&self) -> GuestIpaAddress {
        self.ttbr0
    }

    pub fn get_ttbr_1(&self) -> GuestIpaAddress {
        self.ttbr1
    }

    pub fn get_granule(&self) -> Aarch64TranslationGranule {
        self.translation_table_mgr.get_granule()
    }

    pub fn get_txsz(&self) -> u8 {
        self.translation_table_mgr.get_txsz()
    }

    pub fn allocate_va(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> anyhow::Result<GuestVaAddress> {
        let a = crate::aligner::Aligner::new_from_power_of_two(layout.align() as u64)?;
        let offset = Offset(a.align_up(self.used_va.0));
        let size = layout.size();
        let va = self.dram_va_start.add(offset);
        self.used_va = offset.add(Offset(size as u64));
        trace!(
            "allocated VA address space for {}, {:#x?}, layout size {:?}, align {:#x?}",
            purpose,
            va,
            layout.size(),
            layout.align()
        );
        Ok(va)
    }

    pub fn allocate_ipa(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> anyhow::Result<(*mut u8, GuestIpaAddress)> {
        let a = crate::aligner::Aligner::new_from_power_of_two(layout.align() as u64)?;
        let offset = Offset(a.align_up(self.used_ipa.0));
        let size = layout.size();
        let ipa = self.dram_ipa_start.add(offset);
        let host_ptr = self
            .get_memory_slice_by_ipa(self.dram_ipa_start.add(offset), size)?
            .as_mut_ptr();
        self.used_ipa = offset.add(Offset(size as u64));
        trace!(
            "allocated IPA address space for {}, ipa {:#x?}, layout size {:?}, align {:#x?}",
            purpose,
            ipa.0,
            layout.size(),
            layout.align()
        );
        Ok((host_ptr, ipa))
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P) -> anyhow::Result<LoadedElf> {
        let loaded = elf_loader::load_elf(self, filename)?;
        self.used_ipa = self.used_ipa.add(Offset(loaded.used_dram_size));
        Ok(loaded)
    }

    pub fn get_next_va(&mut self, align: usize) -> anyhow::Result<GuestVaAddress> {
        let aligner = Aligner::new_from_power_of_two(align as u64)?;
        let next_va = self.get_va(self.get_used_va()).0;
        let aligned_next_va = aligner.align_up(next_va);
        if aligned_next_va > next_va {
            self.used_va = self.used_va.add(Offset(aligned_next_va - next_va))
        }
        Ok(self.dram_va_start.add(self.used_va))
    }

    pub fn get_used_va(&self) -> Offset {
        self.used_va
    }

    #[allow(dead_code)]
    pub fn get_used_ipa(&self) -> Offset {
        self.used_ipa
    }

    pub fn get_dram_config(&self) -> Option<DramConfig> {
        self.dram_config
    }

    pub fn configure_dram(&mut self) -> anyhow::Result<()> {
        let ipa = self.dram_ipa_start.add(self.used_ipa);
        let va = self.dram_va_start.add(self.used_va);
        let usable_memory_size = (self.memory_size as u64 - self.used_ipa.0) as usize;
        // This is the RAM that the kernel is free to use for whatever purpose, e.g. allocating.
        debug!(
            "configuring translation tables for DRAM, ipa {:#x?}, va {:#x?}, usable memory size {}",
            ipa.0, va.0, usable_memory_size,
        );

        self.configure_page_tables(ipa, va, usable_memory_size, HvMemoryFlags::ALL)
            .context("error configuring page tables for DRAM")?;
        self.dram_config = Some(DramConfig {
            start_va: va,
            size: usable_memory_size as u64,
        });
        Ok(())
    }

    pub fn get_va(&self, offset: Offset) -> GuestVaAddress {
        self.dram_va_start.add(offset)
    }

    pub fn get_size(&self) -> usize {
        self.memory_size
    }

    pub fn get_memory_slice_by_ipa(
        &self,
        ipa: GuestIpaAddress,
        size: usize,
    ) -> anyhow::Result<&mut [u8]> {
        let vslice = self.memory.get_slice(ipa.as_guest_address(), size)?;
        let ptr = vslice.as_ptr();
        Ok(unsafe { core::slice::from_raw_parts_mut(ptr, size) })
    }

    pub fn get_memory_slice(&self, va: GuestVaAddress, size: usize) -> anyhow::Result<&mut [u8]> {
        let ipa = self
            .simulate_address_lookup(va)?
            .ok_or_else(|| anyhow!("cannot find address {:#x?} in translation tables", va.0))?;
        self.get_memory_slice_by_ipa(ipa, size)
    }

    pub fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        let maybe_ipa = self
            .translation_table_mgr
            .simulate_address_lookup(self, va)?;
        trace!("simulate_address_lookup {:?} => {:?}", va, &maybe_ipa);
        Ok(maybe_ipa)
    }

    pub fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        // This is ridiculous, but a copy is needed here.
        let mgr = self.translation_table_mgr;
        mgr.setup(self, va, ipa, size, flags)
    }
}

impl MemoryManager for GuestMemoryManager {
    fn get_binary_load_address(&mut self) -> GuestVaAddress {
        self.get_next_va(self.translation_table_mgr.get_granule().page_size() as usize)
            .unwrap()
    }
    fn aligner(&self) -> crate::aligner::Aligner {
        self.translation_table_mgr.get_granule().aligner()
    }
    fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        GuestMemoryManager::simulate_address_lookup(self, va)
    }
    fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        GuestMemoryManager::configure_page_tables(self, ipa, va, size, flags)
    }
    fn get_memory_slice(&mut self, va: GuestVaAddress, size: usize) -> anyhow::Result<&mut [u8]> {
        GuestMemoryManager::get_memory_slice(self, va, size)
    }

    fn consume_va(&mut self, size: usize) -> GuestVaAddress {
        self.used_va = self.used_va.add(Offset(size as u64));
        self.get_va(self.used_ipa)
    }

    fn allocate_ipa(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> anyhow::Result<(*mut u8, GuestIpaAddress)> {
        GuestMemoryManager::allocate_ipa(self, layout, purpose)
    }

    fn allocate_va(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> anyhow::Result<GuestVaAddress> {
        GuestMemoryManager::allocate_va(self, layout, purpose)
    }
}
