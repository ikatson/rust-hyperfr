use std::{alloc::Layout, path::Path, sync::Arc};

use vm_memory::GuestMemoryMmap;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset, VaIpa},
    elf_loader::{self, LoadedElf, MemoryManager},
    layout::TTBR_SIZE,
    page_table,
    translation_table::{self, Aarch64PageSize, Table, TranslationTableManager},
    HvMemoryFlags,
};
use anyhow::{anyhow, Context};
use log::{debug, trace};
use vm_memory::GuestMemory;

#[derive(Debug)]
pub struct GuestMemoryManager {
    translation_table_mgr: TranslationTableManager,
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    memory: Arc<GuestMemoryMmap>,
    dram_ipa_start: GuestIpaAddress,
    dram_va_start: GuestVaAddress,
    memory_size: usize,
    usable_memory_offset: Offset,
}

struct TtbrLocation {
    ptr: *mut Table,
    ipa: GuestIpaAddress,
}

impl Default for TtbrLocation {
    fn default() -> Self {
        Self {
            ptr: core::ptr::null_mut(),
            ipa: GuestIpaAddress(0),
        }
    }
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

        let granule = Aarch64PageSize::P16k;
        let txsz = 28;
        let tmp_ttmgr =
            TranslationTableManager::new(granule, txsz, GuestIpaAddress(0), GuestIpaAddress(0))?;

        let mut mm = Self {
            translation_table_mgr: tmp_ttmgr,
            memory,
            dram_ipa_start: ipa_start,
            dram_va_start: va_start,
            memory_size: size,
            // This is temporary
            usable_memory_offset: Offset(0),
            ttbr0: GuestIpaAddress(0),
            ttbr1: GuestIpaAddress(0),
        };

        let ttbr_layout = mm.translation_table_mgr.get_top_ttbr_layout()?;

        let (_, ttbr0) = mm.allocate(ttbr_layout)?;
        let (_, ttbr1) = mm.allocate(ttbr_layout)?;
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

    pub fn allocate(&mut self, layout: Layout) -> anyhow::Result<(*mut u8, GuestIpaAddress)> {
        let a = crate::aligner::Aligner::new_from_power_of_two(layout.align() as u64)?;
        let offset = Offset(a.align_up(self.usable_memory_offset.0));
        let size = layout.size();
        let ipa = self.dram_ipa_start.add(offset);
        let host_ptr = self
            .get_memory_slice_by_ipa(self.dram_ipa_start.add(offset), size)?
            .as_mut_ptr();
        self.usable_memory_offset = offset.add(Offset(size as u64));
        trace!(
            "allocated {} bytes of guest memory, ipa {:#x?}",
            size,
            ipa.0
        );
        Ok((host_ptr, ipa))
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P) -> anyhow::Result<LoadedElf> {
        let loaded = elf_loader::load_elf(self, filename)?;
        self.usable_memory_offset = self.usable_memory_offset.add(Offset(loaded.used_dram_size));
        Ok(loaded)
    }

    pub fn get_usable_memory_offset(&self) -> Offset {
        self.usable_memory_offset
    }

    pub fn configure_dram(&mut self) -> anyhow::Result<()> {
        let ipa = self.dram_ipa_start.add(self.usable_memory_offset);
        let va = self.dram_va_start.add(self.usable_memory_offset);
        let usable_memory_size = (self.memory_size as u64 - self.usable_memory_offset.0) as usize;
        // This is the RAM that the kernel is free to use for whatever purpose, e.g. allocating.
        debug!(
            "configuring translation tables for DRAM, ipa {:#x?}, va {:#x?}, usable memory size {}",
            ipa.0, va.0, usable_memory_size,
        );

        self.configure_page_tables(ipa, va, usable_memory_size, HvMemoryFlags::ALL)
            .context("error configuring page tables for DRAM")?;
        Ok(())
    }

    pub fn get_va(&self, offset: Offset) -> GuestVaAddress {
        self.dram_va_start.add(offset)
    }

    pub fn get_ipa(&self, offset: Offset) -> GuestIpaAddress {
        self.dram_ipa_start.add(offset)
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
    fn get_va(&self, offset: Offset) -> GuestVaAddress {
        GuestMemoryManager::get_va(self, offset)
    }

    fn get_ipa(&self, offset: Offset) -> GuestIpaAddress {
        GuestMemoryManager::get_ipa(self, offset)
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

    fn allocate(&mut self, layout: Layout) -> anyhow::Result<(*mut u8, GuestIpaAddress)> {
        GuestMemoryManager::allocate(self, layout)
    }
}
