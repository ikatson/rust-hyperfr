use crate::HvMemoryFlags;
use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset},
    memory::GuestMemoryManager,
};

use crate::page_table::bits;

enum Aarch64PageSize {
    P4k,
    P16k,
    P64k,
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
    descriptors: [Descriptor; 2048],
}

struct TableMetadata<'a> {
    start: GuestIpaAddress,
    level: u8,
    table: &'a mut Table,
}

struct TranslationTableManager<'a> {
    granule: Aarch64PageSize,
    txsz: u8,
    memory_mgr: &'a GuestMemoryManager,
}

impl<'a> TranslationTableManager<'a> {
    fn get_ttbr_0_address(&self) -> GuestIpaAddress {
        self.memory_mgr.get_ipa(Offset(0))
    }
    fn get_ttbr_1_address(&self) -> GuestIpaAddress {
        self.memory_mgr
            .get_ipa(Offset(core::mem::size_of::<Table>() as u64))
    }
    fn get_ttbr_at(&self, ipa: GuestIpaAddress) -> anyhow::Result<&mut Table> {
        let sz = core::mem::size_of::<Table>();
        let slice = self.memory_mgr.get_memory_slice_by_ipa(ipa, sz)?;
        Ok(unsafe { &mut *(slice.as_mut_ptr() as *mut Table) })
    }

    fn bits_range(&self, table_level: u8) -> (u64, u64) {
        match self.granule {
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

    fn setup(
        &mut self,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let top_bit = (va.0 >> 55) & 1 == 1;
        let initial_level: u8 = { unimplemented!() };
        let table_meta = if top_bit {
            let ipa = self.get_ttbr_1_address();
            let table = self.get_ttbr_at(ipa)?;
            TableMetadata {
                start: ipa,
                level: initial_level,
                table,
            }
        } else {
            let ipa = self.get_ttbr_0_address();
            let table = self.get_ttbr_at(ipa)?;
            TableMetadata {
                start: ipa,
                level: initial_level,
                table,
            }
        };
        unimplemented!()
    }

    fn setup_internal(
        &mut self,
        table: TableMetadata,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        // behave like all the invariants are all set

        let (bt, bl) = self.bits_range(table.level);

        let start_index = bits(va.0, bt, bl) >> bl;
        let end_index = bits(va.add(Offset(size as u64)).0, bt, bl) >> bl;

        for idx in start_index..=end_index {
            let block_size = 1 << bl;
            let block_start = bits(va.0, bt, bl);
            let block_end = block_start + block_size;
            // constrain size for one block
            let size = todo!();
            self.setup_one(table, idx, memory_mgr, va, ipa, size, flags)?;
        }

        // Find out the bits that this table manages.
        // It depends on the level, on the page and TXSZ.
        // Get starting and ending bits, and for each of them, do - setup one, with same args.

        todo!()
    }

    fn setup_one(
        &mut self,
        table: TableMetadata,
        index: u64,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        if table.level == 0 {
            // Just setup a page block and return
            todo!()
        }

        let size_of_block: u64 = todo!();
        if size as u64 == size_of_block {
            // setup as a block
            todo!();
        }

        // Otherwise recurse into the next level.
        let (mut next_level, next_table): (Level, TableMetadata<'_>) =
            self.get_or_allocate_next_level_table(index, memory_mgr)?;

        next_level.setup_internal(next_table, memory_mgr, va, ipa, size, flags)
    }

    fn get_or_allocate_next_level_table(
        &self,
        index: u16,
        memory_mgr: &GuestMemoryManager,
    ) -> anyhow::Result<(Level, TableMetadata<'_>)> {
        todo!()
    }
}

// impl<'a> TranslationTable for Level<'a> {
//     fn simulate_lookup(
//         &self,
//         level: u8,
//         memory_mgr: &GuestMemoryManager,
//         va: GuestVaAddress,
//     ) -> anyhow::Result<Option<GuestIpaAddress>> {
//         todo!()
//     }

//     fn setup(
//         &mut self,
//         memory_mgr: &GuestMemoryManager,
//         table_start_ipa: GuestIpaAddress,
//         va: GuestVaAddress,
//         ipa: GuestIpaAddress,
//         size: usize,
//         flags: HvMemoryFlags,
//     ) -> anyhow::Result<()> {
//         todo!()
//     }
// }
