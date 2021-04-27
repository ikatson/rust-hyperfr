use std::{path::Path, sync::Arc};

use vm_memory::GuestMemoryMmap;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset, VaIpa},
    elf_loader::{self, LoadedElf, MemoryManager},
    layout::TTBR_SIZE,
    page_table, HvMemoryFlags,
};
use anyhow::{anyhow, Context};
use log::debug;
use vm_memory::GuestMemory;

#[derive(Debug)]
pub struct GuestMemoryManager {
    memory: Arc<GuestMemoryMmap>,
    dram_ipa_start: GuestIpaAddress,
    dram_va_start: GuestVaAddress,
    memory_size: usize,
    usable_memory_offset: Offset,
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

        Ok(Self {
            memory,
            dram_ipa_start: ipa_start,
            dram_va_start: va_start,
            memory_size: size,
            // This is temporary
            usable_memory_offset: Self::get_binary_offset(),
        })
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

    fn get_ttbr_0_dram_offset() -> Offset {
        Offset(0)
    }

    pub fn get_ttbr_0(&self) -> GuestIpaAddress {
        self.dram_ipa_start.add(Self::get_ttbr_0_dram_offset())
    }

    pub fn get_ttbr_1(&self) -> GuestIpaAddress {
        self.dram_ipa_start.add(Self::get_ttbr_1_dram_offset())
    }

    fn get_ttbr_1_dram_offset() -> Offset {
        Self::get_ttbr_0_dram_offset().add(Offset(TTBR_SIZE as u64))
    }

    fn get_binary_offset() -> Offset {
        Self::get_ttbr_1_dram_offset().add(Offset(TTBR_SIZE as u64))
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

    unsafe fn get_translation_table_for_va_ptr(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<(GuestIpaAddress, *mut page_table::TranslationTableLevel2_16k)> {
        let top_bit_set = (va.0 >> 55) & 1 == 1;

        let table_start_dram_offset = if top_bit_set {
            Self::get_ttbr_1_dram_offset()
        } else {
            Self::get_ttbr_0_dram_offset()
        };

        let table_ipa = self.get_ipa(table_start_dram_offset);
        let table_ptr = self
            .memory
            .get_slice(table_ipa.as_guest_address(), TTBR_SIZE)
            .with_context(|| format!("error getting slice of memory at {:#x?}", table_ipa.0))?
            .as_ptr() as *mut page_table::TranslationTableLevel2_16k;
        Ok((table_ipa, table_ptr))
    }

    fn get_translation_table_for_va_mut(
        &mut self,
        va: GuestVaAddress,
    ) -> anyhow::Result<(GuestIpaAddress, &mut page_table::TranslationTableLevel2_16k)> {
        unsafe {
            let (ipa, t) = self.get_translation_table_for_va_ptr(va)?;
            Ok((ipa, &mut *t as _))
        }
    }

    fn get_translation_table_for_va(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<(GuestIpaAddress, &page_table::TranslationTableLevel2_16k)> {
        unsafe {
            let (ipa, t) = self.get_translation_table_for_va_ptr(va)?;
            Ok((ipa, &*t as _))
        }
    }

    pub fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        let (ipa, table) = self.get_translation_table_for_va(va)?;
        Ok(table.simulate_lookup(ipa, va))
    }

    pub fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let (table_ipa, table) = self.get_translation_table_for_va_mut(va)?;

        table
            .setup(table_ipa, va, ipa, size, flags)
            .context("error configuring the Level 2 translation table")?;
        Ok(())
    }
}

impl MemoryManager for GuestMemoryManager {
    fn get_binary_load_address(&self) -> VaIpa {
        VaIpa {
            va: self.dram_va_start.add(self.usable_memory_offset),
            ipa: self.dram_ipa_start.add(self.usable_memory_offset),
        }
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
}
