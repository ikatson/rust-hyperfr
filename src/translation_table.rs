use crate::page_table::bits;
use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset},
    memory::GuestMemoryManager,
};
use crate::{aligner::Aligner, HvMemoryFlags};
use anyhow::{anyhow, bail, Context};
use log::{trace, warn};

pub enum Aarch64PageSize {
    P4k,
    P16k,
    P64k,
}

impl Aarch64PageSize {
    const fn page_size_bits(&self) -> u8 {
        match self {
            Aarch64PageSize::P4k => 12,
            Aarch64PageSize::P16k => 14,
            Aarch64PageSize::P64k => 16,
        }
    }
    const fn page_size(&self) -> u64 {
        1 << self.page_size_bits()
    }

    const fn aligner(&self) -> Aligner {
        let mask = !(self.page_size() - 1);
        Aligner::new_from_mask(mask)
    }

    fn initial_level(&self, txsz: u8) -> i8 {
        warn!("rewrite initial_level(), it's a stub now");
        0
    }

    fn block_size(&self, table_level: i8) -> Option<u64> {
        match self {
            Aarch64PageSize::P4k => match table_level {
                _ => unimplemented!(),
            },
            Aarch64PageSize::P16k => match table_level {
                3 => None,
                2 => Some(1 << 25),
                1 => None,
                0 => None,
                _ => unimplemented!(),
            },
            Aarch64PageSize::P64k => match table_level {
                _ => unimplemented!(),
            },
        }
    }

    const fn max_bits_per_level(&self) -> u8 {
        match self {
            Aarch64PageSize::P4k => 9,
            Aarch64PageSize::P16k => 11,
            Aarch64PageSize::P64k => 13,
        }
    }

    fn bits_range(&self, table_level: i8) -> (u64, u64) {
        match self {
            Aarch64PageSize::P4k => match table_level {
                3 => (20, 12),
                2 => (29, 21),
                1 => (38, 30),
                0 => (47, 39),
                _ => unimplemented!(),
            },
            Aarch64PageSize::P16k => match table_level {
                3 => (24, 14),
                2 => (35, 25),
                1 => (46, 36),
                0 => (47, 47),
                _ => unimplemented!(),
            },
            Aarch64PageSize::P64k => match table_level {
                3 => (28, 16),
                2 => (41, 29),
                1 => (47, 42),
                _ => unimplemented!(),
            },
        }
    }
}

pub trait TranslationTable {
    fn simulate_lookup(
        &self,
        level: u8,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>>;
    // fn get_next_level(
    //     &self,
    //     memory_mgr: &GuestMemoryManager,
    //     index: usize,
    // ) -> anyhow::Result<Option<&mut dyn TranslationTable>>;
    fn setup(
        &mut self,
        memory_mgr: &GuestMemoryManager,
        table_start_ipa: GuestIpaAddress,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()>;
}

struct Descriptor(u64);
struct Table {
    // TODO: I guess this is not 2048 for non 16k pages.
    descriptors: [Descriptor; 2048],
}

#[derive(Copy, Clone)]
struct TableMetadata {
    start: GuestIpaAddress,
    level: i8,
    table: *mut Table,
}

impl TableMetadata {
    fn table(&mut self) -> &mut Table {
        unsafe { &mut *self.table }
    }

    fn descriptor(&mut self, idx: usize) -> &mut Descriptor {
        &mut self.table().descriptors[idx]
    }
}

pub struct TranslationTableManager {
    granule: Aarch64PageSize,
    txsz: u8,
}

impl TranslationTableManager {
    pub fn new(granule: Aarch64PageSize, txsz: u8) -> anyhow::Result<Self> {
        Ok(Self { granule, txsz })
    }
    fn get_ttbr_0_address(&self, memory_mgr: &GuestMemoryManager) -> GuestIpaAddress {
        memory_mgr.get_ipa(Offset(0))
    }
    fn get_ttbr_1_address(&self, memory_mgr: &GuestMemoryManager) -> GuestIpaAddress {
        memory_mgr.get_ipa(Offset(core::mem::size_of::<Table>() as u64))
    }
    fn get_ttbr_at(
        &self,
        memory_mgr: &GuestMemoryManager,
        ipa: GuestIpaAddress,
    ) -> anyhow::Result<&mut Table> {
        let sz = core::mem::size_of::<Table>();
        let slice = memory_mgr.get_memory_slice_by_ipa(ipa, sz)?;
        Ok(unsafe { &mut *(slice.as_mut_ptr() as *mut Table) })
    }

    fn get_top_table(
        &self,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<TableMetadata> {
        let top_bit = (va.0 >> 55) & 1 == 1;
        let initial_level: i8 = self.granule.initial_level(self.txsz);
        let table_meta = if top_bit {
            let ipa = self.get_ttbr_1_address(memory_mgr);
            let table = self.get_ttbr_at(memory_mgr, ipa)?;
            TableMetadata {
                start: ipa,
                level: initial_level,
                table,
            }
        } else {
            let ipa = self.get_ttbr_0_address(memory_mgr);
            let table = self.get_ttbr_at(memory_mgr, ipa)?;
            TableMetadata {
                start: ipa,
                level: initial_level,
                table,
            }
        };
        Ok(table_meta)
    }

    pub fn setup(
        &self,
        memory_mgr: &mut GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        // check invariants, then call into setup_internal
        let table = self.get_top_table(memory_mgr, va)?;
        self.setup_internal(table, memory_mgr, va, ipa, size as u64, flags)
    }

    fn setup_internal(
        &self,
        table: TableMetadata,
        memory_mgr: &mut GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        // behave like all the invariants are all set

        let (bt, bl) = self.granule.bits_range(table.level);

        let start_index = bits(va.0, bt, bl) >> bl;
        let end_index = bits(va.add(Offset(size as u64)).0, bt, bl) >> bl;
        let block_size = 1u64 << bl;

        for idx in start_index..=end_index {
            let (va, ipa, size) = {
                let top_bits = bits(!0, 63, bt + 1);
                let index_bits = idx << bl;
                let block_start_va = (va.0 & top_bits) | index_bits;
                trace!(
                    "va={:#x?}, index={}, block_start_va={:#x?}, bt={}, bl={}",
                    va.0,
                    idx,
                    block_start_va,
                    bt,
                    bl
                );
                let block_end_va = block_start_va + block_size;
                let va_this_block = va.0.max(block_start_va);
                let va_this_block_end = block_end_va.min(va.0 + size);
                let size = va_this_block_end - va_this_block;
                let ipa = ipa.add(Offset(va_this_block - va.0));
                (GuestVaAddress(va_this_block), ipa, size)
            };
            self.setup_one(table, idx as u16, memory_mgr, va, ipa, size, flags)?;
        }

        Ok(())
    }

    fn setup_one(
        &self,
        mut table: TableMetadata,
        index: u16,
        memory_mgr: &mut GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        trace!(
            "setup_one: table.level={}, table.ipa={:#x?}, index={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
            table.level, table.start.0, index, va.0, ipa.0, size, flags
        );
        if table.level == 3 {
            trace!(
                "writing l3={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
                index,
                va.0,
                ipa.0,
                size,
                flags
            );
            let d = table.descriptor(index as usize);
            let mut v: u64 = 0b11;
            v |= 1 << 10; // AF=1
            v |= 0b10 << 8; // SH
            v |= ipa.0;

            if !(flags.contains(HvMemoryFlags::HV_MEMORY_EXEC)) {
                v |= 1 << 53; // Privileged execute never
            }

            // AP bits AP[2:1], bits[7:6] Data Access Permissions bits, see Memory access control on page D5-2731.
            if !flags.contains(HvMemoryFlags::HV_MEMORY_WRITE) {
                v |= 0b10 << 6;
            }

            d.0 = v;
            return Ok(());
        }

        if let Some(block_size) = self.granule.block_size(table.level) {
            if size as u64 == block_size {
                let level = table.level;
                let d = table.descriptor(index as usize);

                if d.0 & 0b11 != 0 {
                    bail!("L{} table {} already set-up", level, index);
                }

                // Block
                d.0 = 0b01;
                d.0 |= 1 << 10; // AF=1
                d.0 |= ipa.0;

                d.0 |= 0b10 << 8; // SH
                if !(flags.contains(HvMemoryFlags::HV_MEMORY_EXEC)) {
                    d.0 |= 1 << 53; // Privileged execute never
                    d.0 |= 1 << 54; // Unprivileged execute never
                }

                // AP bits AP[2:1], bits[7:6] Data Access Permissions bits, see Memory access control on page D5-2731.
                if !flags.contains(HvMemoryFlags::HV_MEMORY_WRITE) {
                    d.0 |= 0b10 << 6;
                }

                trace!(
                    "block: l{}={}, val={:#x?}, va: {:#x?}, ipa: {:#x?}, flags: {:?}",
                    level,
                    index,
                    d.0,
                    va.0,
                    ipa.0,
                    flags
                );
                return Ok(());
            }
        }

        // Otherwise recurse into the next level.
        let next_table = self.get_or_allocate_next_level_table(table, index, memory_mgr)?;
        self.setup_internal(next_table, memory_mgr, va, ipa, size, flags)
    }

    fn get_or_allocate_next_level_table(
        &self,
        mut table: TableMetadata,
        index: u16,
        memory_mgr: &mut GuestMemoryManager,
    ) -> anyhow::Result<TableMetadata> {
        let level = table.level;
        let descriptor = table.descriptor(index as usize);
        match descriptor.0 & 0b11 {
            0b01 => {
                bail!("already a block")
            }
            0b11 => {
                let ipa = bits(descriptor.0, 47, self.granule.page_size_bits() as u64);
                let ipa = GuestIpaAddress(ipa);
                let table_ptr = memory_mgr
                    .get_memory_slice_by_ipa(ipa, core::mem::size_of::<Table>())?
                    .as_mut_ptr() as *mut Table;
                Ok(TableMetadata {
                    level: level + 1,
                    table: table_ptr,
                    start: ipa,
                })
            }
            0b00 => {
                let layout = core::alloc::Layout::from_size_align(
                    core::mem::size_of::<Table>(),
                    1 << self.granule.max_bits_per_level(),
                )?;
                let (ptr, ipa) = memory_mgr.allocate(layout)?;

                trace!("writing l{}={}, next ipa={:#x?}", level, index, ipa.0,);

                descriptor.0 |= 0b11;
                descriptor.0 |= ipa.0;
                Ok(TableMetadata {
                    level: level + 1,
                    table: ptr as *mut _,
                    start: ipa,
                })
            }
            _ => bail!("bullshit"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_1() {
        pretty_env_logger::init();
        let va = GuestVaAddress(0xf000_0000_0000);
        let ipa = GuestIpaAddress(0x0);
        let memory_size = 4 * 1024 * 1024 * 1024;

        let mut mgr = crate::GuestMemoryManager::new(va, ipa, memory_size).unwrap();
        let ttmgr = TranslationTableManager::new(Aarch64PageSize::P16k, 28).unwrap();

        // Setup identity mapping with offset.
        let offset = GuestVaAddress(0x0000_ffff_0000_0000);
        ttmgr
            .setup(&mut mgr, offset, ipa, 48 * 1024 * 1024, HvMemoryFlags::ALL)
            .unwrap()
    }
}
