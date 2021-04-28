use std::alloc::Layout;

use crate::page_table::bits;
use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset},
    memory::GuestMemoryManager,
};
use crate::{aligner::Aligner, HvMemoryFlags};
use anyhow::{anyhow, bail, Context};
use log::{trace, warn};

#[derive(Debug, Copy, Clone)]
pub enum Aarch64PageSize {
    P4k,
    P16k,
    P64k,
}

impl Aarch64PageSize {
    pub const fn page_size_bits(&self) -> u8 {
        match self {
            Aarch64PageSize::P4k => 12,
            Aarch64PageSize::P16k => 14,
            Aarch64PageSize::P64k => 16,
        }
    }
    pub const fn page_size(&self) -> u64 {
        1 << self.page_size_bits()
    }

    pub const fn aligner(&self) -> Aligner {
        let mask = !(self.page_size() - 1);
        Aligner::new_from_mask(mask)
    }

    pub fn initial_level(&self, txsz: u8) -> i8 {
        warn!("rewrite initial_level(), it's a stub now");
        2
    }

    pub fn block_size_bits(&self, table_level: i8) -> Option<u8> {
        match self {
            Aarch64PageSize::P4k => match table_level {
                _ => unimplemented!(),
            },
            Aarch64PageSize::P16k => match table_level {
                3 => None,
                2 => Some(25),
                1 => None,
                0 => None,
                _ => unimplemented!(),
            },
            Aarch64PageSize::P64k => match table_level {
                _ => unimplemented!(),
            },
        }
    }

    pub fn block_size(&self, table_level: i8) -> Option<u64> {
        self.block_size_bits(table_level).map(|b| 1 << b)
    }

    pub const fn max_bits_per_level(&self) -> u8 {
        match self {
            Aarch64PageSize::P4k => 9,
            Aarch64PageSize::P16k => 11,
            Aarch64PageSize::P64k => 13,
        }
    }

    pub fn bits_range(&self, table_level: i8) -> (u64, u64) {
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

struct Descriptor(u64);
pub struct Table {
    // TODO: I guess this is not 2048 for non 16k pages.
    // Furthermore, for level 1 16k page this only could hold 2 values, not 2048.
    // Others are just wasted space.
    descriptors: [Descriptor; 2048],
}

#[derive(Copy, Clone)]
struct TableMetadata {
    start: GuestIpaAddress,
    level: i8,
    table: *mut Table,
}

impl TableMetadata {
    fn table(&self) -> &Table {
        unsafe { &*self.table }
    }

    fn table_mut(&mut self) -> &mut Table {
        unsafe { &mut *self.table }
    }

    fn descriptor(&self, idx: usize) -> &Descriptor {
        &self.table().descriptors[idx]
    }

    fn descriptor_mut(&mut self, idx: usize) -> &mut Descriptor {
        &mut self.table_mut().descriptors[idx]
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TranslationTableManager {
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    granule: Aarch64PageSize,
    txsz: u8,
}

impl TranslationTableManager {
    pub fn new(
        granule: Aarch64PageSize,
        txsz: u8,
        ttbr0: GuestIpaAddress,
        ttbr1: GuestIpaAddress,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            ttbr0,
            ttbr1,
            granule,
            txsz,
        })
    }

    pub fn get_top_ttbr_layout(&self) -> anyhow::Result<Layout> {
        Ok(Layout::from_size_align(
            core::mem::size_of::<Table>(),
            self.granule.page_size() as usize,
        )?)
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
            let ipa = self.ttbr1;
            let table = self.get_ttbr_at(memory_mgr, ipa)?;
            TableMetadata {
                start: ipa,
                level: initial_level,
                table,
            }
        } else {
            let ipa = self.ttbr0;
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

        let aligner = self.granule.aligner();
        if !aligner.is_aligned(va.0) {
            bail!("{:?} is not aligned", va)
        }
        if !aligner.is_aligned(ipa.0) {
            bail!("{:?} is not aligned", ipa)
        }
        if !aligner.is_aligned(size as u64) {
            bail!("size {:#x?} is not aligned", size)
        }

        self.setup_internal(table, memory_mgr, va, ipa, size as u64, flags)
    }

    pub fn simulate_address_lookup(
        &self,
        mm: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        let mut table = self.get_top_table(mm, va)?;
        trace!(
            "simulate_address_lookup {:?}, starting at level {}, table at {:?}",
            va,
            table.level,
            table.start
        );
        loop {
            trace!(
                "simulate_address_lookup {:?}, level {}, table at {:?}",
                va,
                table.level,
                table.start
            );
            let (bt, bb) = self.granule.bits_range(table.level);
            let index = bits(va.0, bt, bb) >> bb;
            let d = table.descriptor(index as usize);
            match d.0 & 0b11 {
                0b11 => {
                    let psb = self.granule.page_size_bits() as u64;
                    let ipa = GuestIpaAddress(bits(d.0, 47, psb));
                    trace!("descriptor ipa at level {}: {:?}", table.level, ipa);
                    if table.level == 3 {
                        let offset = Offset(va.0 & ((1 << psb) - 1));
                        return Ok(Some(ipa.add(offset)));
                    }
                    let table_ptr = mm
                        .get_memory_slice_by_ipa(ipa, core::mem::size_of::<Table>())?
                        .as_mut_ptr() as *mut Table;
                    table = TableMetadata {
                        level: table.level + 1,
                        table: table_ptr,
                        start: ipa,
                    }
                }
                0b01 => {
                    let block_size_bits = match self.granule.block_size_bits(table.level) {
                        Some(bs) => bs,
                        None => {
                            bail!(
                                "saw a block on level {}, this should not have happened",
                                table.level
                            );
                        }
                    };
                    let ipa = GuestIpaAddress(bits(d.0, 47, block_size_bits as u64));
                    trace!("descriptor block ipa at level {}: {:?}", table.level, ipa);
                    let offset = Offset(va.0 & ((1 << block_size_bits) - 1));
                    return Ok(Some(ipa.add(offset)));
                }
                _ => return Ok(None),
            }
        }
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
        debug_assert!(self.granule.aligner().is_aligned(va.0));
        debug_assert!(self.granule.aligner().is_aligned(ipa.0));
        debug_assert!(size > 0);
        debug_assert!(self.granule.aligner().is_aligned(size as u64));

        let (bt, bl) = self.granule.bits_range(table.level);

        let start_index = bits(va.0, bt, bl) >> bl;
        let end_index = bits(va.add(Offset((size - 1) as u64)).0, bt, bl) >> bl;
        let block_size = 1u64 << bl;

        trace!(
            "setup_internal: table.level={}, table.ipa={:#x?}, start_index={}, end_index={}, bt={}, bl={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
            table.level, table.start.0, start_index, end_index, bt, bl, va.0, ipa.0, size, flags
        );

        for idx in start_index..=end_index {
            let (va, ipa, size) = {
                let top_bits = bits(!0, 63, bt + 1);
                let index_bits = idx << bl;
                let block_start_va = (va.0 & top_bits) | index_bits;

                let (va, ipa, size) = if va.0 < block_start_va {
                    let new_va = block_start_va;
                    let offset = Offset(block_start_va - va.0);
                    let ipa = ipa.add(offset);
                    let size = (size - offset.0).min(block_size);
                    (new_va, ipa, size)
                } else {
                    // The only reason this could be happening is that va is inside the block.
                    let va = va.0;
                    let offset = Offset(va - block_start_va);
                    let ipa = ipa;
                    let size = size.min(block_size - offset.0);
                    (va, ipa, size)
                };
                (GuestVaAddress(va), ipa, size)
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

        debug_assert!(self.granule.aligner().is_aligned(va.0));
        debug_assert!(self.granule.aligner().is_aligned(ipa.0));
        debug_assert!(size > 0);
        debug_assert!(self.granule.aligner().is_aligned(size as u64));

        if table.level == 3 {
            trace!(
                "writing l3={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
                index,
                va.0,
                ipa.0,
                size,
                flags
            );
            let d = table.descriptor_mut(index as usize);
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
                let d = table.descriptor_mut(index as usize);

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
        let descriptor = table.descriptor_mut(index as usize);
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
                trace!(
                    "will allocate memory for table level {}, index {}, layout {:?}",
                    level,
                    index,
                    &layout
                );
                let (ptr, ipa) = memory_mgr.allocate(layout)?;
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

// #[cfg(test)]
// mod tests {
//     use super::*;
//     #[test]
//     fn test_1() {
//         pretty_env_logger::init();
//         let va = GuestVaAddress(0xf000_0000_0000);
//         let ipa = GuestIpaAddress(0x0);
//         let memory_size = 4 * 1024 * 1024 * 1024;

//         let mut mgr = crate::GuestMemoryManager::new(va, ipa, memory_size).unwrap();
//         let ttmgr = TranslationTableManager::new(Aarch64PageSize::P16k, 28).unwrap();

//         // Setup identity mapping with offset.
//         // let offset = GuestVaAddress(0x0000_ffff_0000_0000);
//         let offset = GuestVaAddress(0);
//         ttmgr
//             .setup(
//                 &mut mgr,
//                 offset,
//                 ipa,
//                 32 * 1024 * 1024 + 16384,
//                 HvMemoryFlags::ALL,
//             )
//             .unwrap()
//     }
// }
