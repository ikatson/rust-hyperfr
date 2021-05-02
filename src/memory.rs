use std::{
    alloc::Layout,
    path::Path,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::vm_memory::GuestMemoryMmap;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset},
    elf_loader::{self, LoadedElf, MemoryManager},
    translation_table::{new_tt_mgr, Aarch64TranslationGranule, Granule, TtMgr},
    HvMemoryFlags,
};
use anyhow::{anyhow, bail, Context};
use log::{debug, trace};

#[derive(Debug, Clone, Copy)]
pub struct DramConfig {
    pub start_va: GuestVaAddress,
    pub size: u64,
}

#[derive(Debug)]
pub struct GuestMemoryManager {
    translation_table_mgr: Box<dyn TtMgr>,
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    memory: GuestMemoryMmap,
    dram_ipa_start: GuestIpaAddress,
    dram_va_start: GuestVaAddress,
    memory_size: usize,
    used_ipa: AtomicU64,
    used_va: AtomicU64,
    dram_config: Option<DramConfig>,
}

impl GuestMemoryManager {
    pub fn new(
        va_start: GuestVaAddress,
        ipa_start: GuestIpaAddress,
        size: usize,
    ) -> crate::Result<Self> {
        let memory =
            GuestMemoryMmap::new(ipa_start, size).context("error allocating guest memory")?;

        let granule = match std::env::var("GRANULE").as_deref().unwrap_or_default() {
            "4" => Aarch64TranslationGranule::P4k,
            "" | "16" => Aarch64TranslationGranule::P16k,
            other => bail!("GRANULE={} is not supported, try 4,16 or 64", other),
        };
        let txsz: u8 = match std::env::var("TXSZ") {
            Ok(v) => v
                .parse()
                .with_context(|| format!("error parsing envvar TXSZ={} as u8", &v))?,
            Err(_) => 28,
        };
        let tmp_ttmgr = new_tt_mgr(GuestIpaAddress(0), GuestIpaAddress(1), granule, txsz)?;

        let mut mm = Self {
            translation_table_mgr: tmp_ttmgr,
            memory,
            dram_ipa_start: ipa_start,
            dram_va_start: va_start,
            memory_size: size,
            used_ipa: AtomicU64::new(0),
            used_va: AtomicU64::new(0),
            // This is temporary
            ttbr0: GuestIpaAddress(0),
            ttbr1: GuestIpaAddress(0),
            dram_config: None,
        };

        let ttbr_layout = mm.translation_table_mgr.get_top_ttbr_layout()?;

        let (_, ttbr0) = mm.allocate_ipa(ttbr_layout, format_args!("TTBR0"))?;
        let (_, ttbr1) = mm.allocate_ipa(ttbr_layout, format_args!("TTBR1"))?;
        mm.translation_table_mgr = new_tt_mgr(ttbr0, ttbr1, granule, txsz)?;
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

    pub fn get_granule(&self) -> &'static dyn Granule {
        self.translation_table_mgr.get_granule()
    }

    pub fn get_txsz(&self) -> u8 {
        self.translation_table_mgr.get_txsz()
    }

    pub fn allocate_va(
        &self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> crate::Result<GuestVaAddress> {
        loop {
            let used_va = self.used_va.load(Ordering::Relaxed);
            let a = crate::aligner::Aligner::new_from_power_of_two(layout.align() as u64)?;
            let offset = Offset(a.align_up(used_va));
            let size = layout.size();
            let va = self.dram_va_start.add(offset);
            let new = offset.0 + size as u64;
            if self
                .used_va
                .compare_exchange(used_va, new, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
            {
                trace!(
                    "allocated VA address space for {}, {:#x?}, layout size {:?}, align {:#x?}",
                    purpose,
                    va,
                    layout.size(),
                    layout.align()
                );
                return Ok(va);
            }
        }
    }

    pub fn allocate_ipa(
        &self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> crate::Result<(*mut u8, GuestIpaAddress)> {
        let a = crate::aligner::Aligner::new_from_power_of_two(layout.align() as u64)?;
        loop {
            let used_ipa = self.used_ipa.load(Ordering::Relaxed);
            let offset = Offset(a.align_up(used_ipa));
            let size = layout.size();
            let ipa = self.dram_ipa_start.add(offset);
            if self
                .used_ipa
                .compare_exchange(
                    used_ipa,
                    offset.0 + size as u64,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                let host_ptr = self
                    .get_memory_slice_by_ipa(self.dram_ipa_start.add(offset), size)?
                    .as_mut_ptr();

                trace!(
                    "allocated IPA address space for {}, ipa {:#x?}, layout size {:?}, align {:#x?}",
                    purpose,
                    ipa.0,
                    layout.size(),
                    layout.align()
                );
                return Ok((host_ptr, ipa));
            }
        }
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P) -> crate::Result<LoadedElf> {
        elf_loader::load_elf(self, filename)
    }

    pub fn get_dram_config(&self) -> Option<DramConfig> {
        self.dram_config
    }

    pub fn configure_dram(&mut self) -> crate::Result<()> {
        let used_ipa = Offset(self.used_ipa.load(Ordering::Relaxed));
        let ipa = self.dram_ipa_start.add(used_ipa);
        let va = self
            .dram_va_start
            .add(Offset(self.used_va.load(Ordering::Relaxed)));
        let usable_memory_size = (self.memory_size as u64 - used_ipa.0) as usize;
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
    ) -> crate::Result<&mut [u8]> {
        self.memory
            .get_slice(ipa, size)
            .ok_or_else(|| anyhow!("cannot get memory at address {:?}", ipa))
    }

    pub fn get_memory_slice(&self, va: GuestVaAddress, size: usize) -> crate::Result<&mut [u8]> {
        let ipa = self
            .simulate_address_lookup(va)?
            .ok_or_else(|| anyhow!("cannot find address {:#x?} in translation tables", va.0))?;
        self.get_memory_slice_by_ipa(ipa, size)
    }

    pub fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> crate::Result<Option<GuestIpaAddress>> {
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
    ) -> crate::Result<()> {
        self.translation_table_mgr.setup(self, va, ipa, size, flags)
    }
}

impl MemoryManager for GuestMemoryManager {
    fn aligner(&self) -> crate::aligner::Aligner {
        self.translation_table_mgr.get_granule().aligner()
    }
    fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> crate::Result<Option<GuestIpaAddress>> {
        GuestMemoryManager::simulate_address_lookup(self, va)
    }
    fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> crate::Result<()> {
        GuestMemoryManager::configure_page_tables(self, ipa, va, size, flags)
    }
    fn get_memory_slice(&mut self, va: GuestVaAddress, size: usize) -> crate::Result<&mut [u8]> {
        GuestMemoryManager::get_memory_slice(self, va, size)
    }

    fn allocate_ipa(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> crate::Result<(*mut u8, GuestIpaAddress)> {
        GuestMemoryManager::allocate_ipa(self, layout, purpose)
    }

    fn allocate_va(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> crate::Result<GuestVaAddress> {
        GuestMemoryManager::allocate_va(self, layout, purpose)
    }
}
