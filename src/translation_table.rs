use std::alloc::Layout;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress, Offset},
    memory::GuestMemoryManager,
};
use crate::{aligner::Aligner, HvMemoryFlags};
use anyhow::bail;
use log::trace;

pub const fn bits(val: u64, start_inclusive: u8, end_inclusive: u8) -> u64 {
    let top_mask = match start_inclusive {
        63 => u64::MAX,
        0..=62 => (1u64 << (start_inclusive + 1)) - 1,
        _ => 0,
    };
    let bottom_mask = !((1 << end_inclusive) - 1);
    val & top_mask & bottom_mask
}

pub trait Granule: core::fmt::Debug + Send + Sync {
    fn get_dyn_self(&self) -> &'static dyn Granule;
    fn tg0_bits(&self) -> u64;
    fn tg1_bits(&self) -> u64;
    fn page_size_bits(&self) -> u8;
    fn page_size(&self) -> u64 {
        1 << self.page_size_bits()
    }
    fn aligner(&self) -> Aligner {
        let mask = !(self.page_size() - 1);
        Aligner::new_from_mask(mask)
    }
    fn layout_for_level(&self, level: i8, txsz: u8) -> Layout {
        let (bt, bl) = self.bits_range(level, txsz);
        let stride = bt - bl + 1;
        let size = core::mem::size_of::<Descriptor>() * (1 << stride);
        let align = 1 << self.page_size_bits();
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }
    fn initial_level(&self, txsz: u8) -> i8;
    fn block_size_bits(&self, table_level: i8) -> Option<u8>;
    fn block_size(&self, table_level: i8) -> Option<u64> {
        // Can't use map in const fn.
        self.block_size_bits(table_level).map(|b| 1 << b)
    }
    fn max_stride(&self) -> u8 {
        self.page_size_bits() - 3
    }
    fn bits_range(&self, table_level: i8, txsz: u8) -> (u8, u8) {
        // Copied this code from TTBRWALK.txt
        let initial_level = self.initial_level(txsz);

        let grainsize = self.page_size_bits();
        let stride = self.max_stride();

        let addrselectbottom = (3 - table_level) as u8 * stride + grainsize;
        let addrselecttop = if table_level == initial_level {
            (64 - txsz) - 1
        } else {
            addrselectbottom + stride - 1
        };
        (addrselecttop, addrselectbottom)
    }
}

static GRANULE_4K: &'static dyn Granule = &Granule4k {};
static GRANULE_16K: &'static dyn Granule = &Granule16k {};

#[derive(Debug)]
struct Granule4k {}
#[derive(Debug)]
struct Granule16k {}

impl Granule for Granule4k {
    fn get_dyn_self(&self) -> &'static dyn Granule {
        GRANULE_4K
    }
    fn tg0_bits(&self) -> u64 {
        0
    }
    fn tg1_bits(&self) -> u64 {
        0b10 << 30
    }
    fn page_size_bits(&self) -> u8 {
        14
    }

    fn initial_level(&self, txsz: u8) -> i8 {
        match txsz {
            12..=15 => -1,
            16..=24 => 0,
            25..=33 => 1,
            34..=42 => 2,
            43..=48 => 3,
            _ => i8::MIN,
        }
    }

    fn block_size_bits(&self, table_level: i8) -> Option<u8> {
        match table_level {
            2 => Some(21),
            1 => Some(30),
            _ => None,
        }
    }
}

impl Granule for Granule16k {
    fn get_dyn_self(&self) -> &'static dyn Granule {
        GRANULE_16K
    }
    fn tg0_bits(&self) -> u64 {
        0b10 << 14
    }
    fn tg1_bits(&self) -> u64 {
        0b01 << 30
    }
    fn page_size_bits(&self) -> u8 {
        14
    }

    fn initial_level(&self, txsz: u8) -> i8 {
        match txsz {
            12..=16 => 0,
            17..=27 => 1,
            28..=38 => 2,
            39..=48 => 3,
            _ => i8::MIN,
        }
    }

    fn block_size_bits(&self, table_level: i8) -> Option<u8> {
        match table_level {
            2 => Some(25),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Aarch64TranslationGranule {
    P4k,
    P16k,
    #[allow(dead_code)]
    P64k,
}
struct Descriptor(u64);

#[derive(Copy, Clone, Debug)]
struct TableMetadata {
    start: GuestIpaAddress,
    level: i8,
    descriptors: *mut Descriptor,
}

unsafe impl Sync for TableMetadata {}
unsafe impl Send for TableMetadata {}

impl TableMetadata {
    fn descriptor(&self, idx: usize) -> &Descriptor {
        unsafe { &*(self.descriptors.add(idx)) }
    }

    fn descriptor_mut(&mut self, idx: usize) -> &mut Descriptor {
        unsafe { &mut *(self.descriptors.add(idx)) }
    }
}

pub trait TtMgr: core::fmt::Debug + Send + Sync {
    fn get_top_ttbr_layout(&self) -> anyhow::Result<Layout>;
    fn setup(
        &self,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()>;
    fn simulate_address_lookup(
        &self,
        mm: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>>;
    fn get_granule(&self) -> &'static dyn Granule;
    fn get_txsz(&self) -> u8;
}

impl<G: Granule + Send + Sync + core::fmt::Debug> TtMgr for TranslationTableManager<G> {
    fn get_top_ttbr_layout(&self) -> anyhow::Result<Layout> {
        Self::get_top_ttbr_layout(&self)
    }

    fn setup(
        &self,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        Self::setup(&self, memory_mgr, va, ipa, size, flags)
    }

    fn simulate_address_lookup(
        &self,
        mm: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        Self::simulate_address_lookup(&self, mm, va)
    }

    fn get_granule(&self) -> &'static dyn Granule {
        Self::get_granule(&self)
    }

    fn get_txsz(&self) -> u8 {
        Self::get_txsz(&self)
    }
}

pub fn new_tt_mgr(
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    granule: Aarch64TranslationGranule,
    txsz: u8,
) -> anyhow::Result<Box<dyn TtMgr>> {
    match granule {
        Aarch64TranslationGranule::P4k => Ok(Box::new(TranslationTableManager::new(
            Granule4k {},
            txsz,
            ttbr0,
            ttbr1,
        )?)),
        Aarch64TranslationGranule::P16k => Ok(Box::new(TranslationTableManager::new(
            Granule16k {},
            txsz,
            ttbr0,
            ttbr1,
        )?)),
        Aarch64TranslationGranule::P64k => bail!("granule 64k not implemented"),
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TranslationTableManager<G> {
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    granule: G,
    ips_size: u64,
    ips_bits: u8,
    txsz: u8,
}

impl<G: Granule> TranslationTableManager<G> {
    fn new(
        granule: G,
        txsz: u8,
        ttbr0: GuestIpaAddress,
        ttbr1: GuestIpaAddress,
    ) -> anyhow::Result<Self> {
        let ips_bits = 36;
        let ips_size = 1 << ips_bits;
        Ok(Self {
            ttbr0,
            ttbr1,
            granule,
            ips_size,
            ips_bits,
            txsz,
        })
    }

    fn initial_level(&self) -> i8 {
        self.granule.initial_level(self.txsz)
    }

    fn layout_for_level(&self, level: i8) -> Layout {
        self.granule.layout_for_level(level, self.txsz)
    }

    pub fn get_granule(&self) -> &'static dyn Granule {
        self.granule.get_dyn_self()
    }

    pub fn get_txsz(&self) -> u8 {
        self.txsz
    }

    pub fn get_top_ttbr_layout(&self) -> anyhow::Result<Layout> {
        Ok(self.layout_for_level(self.initial_level()))
    }

    fn get_ttbr_at(
        &self,
        memory_mgr: &GuestMemoryManager,
        ipa: GuestIpaAddress,
    ) -> anyhow::Result<TableMetadata> {
        let sz = self.get_top_ttbr_layout()?.size();
        let slice = memory_mgr.get_memory_slice_by_ipa(ipa, sz)?;
        Ok(TableMetadata {
            level: self.initial_level(),
            descriptors: slice.as_mut_ptr() as *mut Descriptor,
            start: ipa,
        })
    }

    fn get_top_table(
        &self,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<TableMetadata> {
        let top_bit = (va.0 >> 55) & 1 == 1;
        let ipa = if top_bit { self.ttbr1 } else { self.ttbr0 };

        // Just a double-check for debugging
        // In pseudo-code this was:
        // if !IsZero(baseregister < 47: outputsize > ) -> throw AddressFault
        debug_assert_eq!(bits(ipa.0, 47, self.ips_bits), 0);

        if top_bit {
            // Make sure all bits <top:inputsize> are ones.
            // where inputsize = 64 - TxSZ and top=55
            if bits(va.0, 55, 64 - self.txsz) != bits(u64::MAX, 55, 64 - self.txsz) {
                bail!(
                    "bits [64:{}] should be 1, but they are not in {:?}",
                    (64 - self.txsz),
                    va
                )
            }
        } else {
            // Make sure all bits up to TXSZ are zeroes.
            if bits(va.0, 55, 64 - self.txsz) != 0 {
                bail!(
                    "bits [64:{}] should be zeroes, but they are not in {:?}",
                    (64 - self.txsz),
                    va
                )
            }
        }

        self.get_ttbr_at(memory_mgr, ipa)
    }

    pub fn setup(
        &self,
        memory_mgr: &GuestMemoryManager,
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

        match ipa.0.checked_add(size as u64) {
            Some(ipa_end) => {
                if ipa_end >= self.ips_size {
                    bail!(
                        "ipa {:#x?} / and or ipa + size are too large, does not fit into the TXSZ
                        space which is limited by address {:#x?}",
                        ipa,
                        self.ips_size - 1
                    )
                }
            }
            None => bail!("ipa + size overflow, {:?}, size {:?}", ipa, size),
        };

        self.setup_internal(table, memory_mgr, va, ipa, size as u64, flags)
    }

    pub fn simulate_address_lookup(
        &self,
        mm: &GuestMemoryManager,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        let mut table = self.get_top_table(mm, va)?;
        loop {
            let (bt, bb) = self.granule.bits_range(table.level, self.txsz);
            let index = bits(va.0, bt, bb) >> bb;
            let d = table.descriptor(index as usize);
            trace!(
                "simulate_address_lookup: va={:?}, table={:?}, index={}, d.value={:#x?}",
                va,
                &table,
                index,
                d.0
            );
            match d.0 & 0b11 {
                0b11 => {
                    let psb = self.granule.page_size_bits();
                    let ipa = GuestIpaAddress(bits(d.0, 47, psb));
                    if table.level == 3 {
                        let offset = Offset(va.0 & ((1 << psb) - 1));
                        return Ok(Some(ipa.add(offset)));
                    }
                    let table_ptr = mm
                        .get_memory_slice_by_ipa(
                            ipa,
                            self.layout_for_level(table.level + 1).size(),
                        )?
                        .as_mut_ptr() as *mut Descriptor;
                    table = TableMetadata {
                        level: table.level + 1,
                        descriptors: table_ptr,
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
                    let ipa = GuestIpaAddress(bits(d.0, 47, block_size_bits));
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
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        debug_assert!(self.granule.aligner().is_aligned(va.0));
        debug_assert!(self.granule.aligner().is_aligned(ipa.0));
        debug_assert!(size > 0);
        debug_assert!(self.granule.aligner().is_aligned(size as u64));

        let (bt, bl) = self.granule.bits_range(table.level, self.txsz);

        let start_index = bits(va.0, bt, bl) >> bl;
        let end_index = bits(va.add(Offset((size - 1) as u64)).0, bt, bl) >> bl;
        let block_size = 1u64 << bl;

        trace!(
            "setup_internal: table.level={}, table.ipa={:#x?}, start_index={}, end_index={}, bt={}, bl={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
            table.level, table.start.0, start_index, end_index, bt, bl, va.0, ipa.0, size, flags
        );

        use rayon::prelude::*;

        (start_index..=end_index)
            .into_par_iter()
            .try_for_each(|idx| {
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
                self.setup_one(table, idx as u16, memory_mgr, va, ipa, size, flags)
            })?;

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn setup_one(
        &self,
        mut table: TableMetadata,
        index: u16,
        memory_mgr: &GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        debug_assert!(self.granule.aligner().is_aligned(va.0));
        debug_assert!(self.granule.aligner().is_aligned(ipa.0));
        debug_assert!(size > 0);
        debug_assert!(self.granule.aligner().is_aligned(size as u64));

        // If a page table, just setup, i.e. end recursion.
        if table.level == 3 {
            let d = table.descriptor_mut(index as usize);

            if d.0 & 0b11 != 0 {
                bail!(
                    "page already set up. Old value {:#x?}, l3={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
                    d.0,
                    index,
                    va,
                    ipa,
                    size,
                    flags
                );
            }

            trace!(
                "writing page l3={}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}",
                index,
                va.0,
                ipa.0,
                size,
                flags
            );

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

        // If size is equal to the block size required for this level, setup a block.
        if self
            .granule
            .block_size(table.level)
            .map(|bs| bs == size)
            .unwrap_or_default()
        {
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
                "writing block: l{}={}, val={:#x?}, va: {:#x?}, ipa: {:#x?}, flags: {:?}",
                level,
                index,
                d.0,
                va.0,
                ipa.0,
                flags
            );
            return Ok(());
        }

        // Otherwise recurse into the next level.
        let next_table = self.get_or_allocate_next_level_table(table, index, memory_mgr)?;
        self.setup_internal(next_table, memory_mgr, va, ipa, size, flags)
    }

    fn get_or_allocate_next_level_table(
        &self,
        mut table: TableMetadata,
        index: u16,
        memory_mgr: &GuestMemoryManager,
    ) -> anyhow::Result<TableMetadata> {
        let level = table.level;
        let descriptor = table.descriptor_mut(index as usize);
        match descriptor.0 & 0b11 {
            0b01 => {
                bail!("already a block")
            }
            0b11 => {
                let ipa = bits(descriptor.0, 47, self.granule.page_size_bits());
                let ipa = GuestIpaAddress(ipa);
                let table_ptr = memory_mgr
                    .get_memory_slice_by_ipa(ipa, self.layout_for_level(level + 1).size())?
                    .as_mut_ptr() as *mut Descriptor;
                Ok(TableMetadata {
                    level: level + 1,
                    descriptors: table_ptr,
                    start: ipa,
                })
            }
            0b00 => {
                let layout = self.layout_for_level(level + 1);
                let (ptr, ipa) = memory_mgr.allocate_ipa(
                    layout,
                    format_args!("translation table level {}, index {}", level, index),
                )?;
                descriptor.0 |= 0b11;
                descriptor.0 |= ipa.0;
                Ok(TableMetadata {
                    level: level + 1,
                    descriptors: ptr as *mut _,
                    start: ipa,
                })
            }
            _ => bail!("memory is corrupted, this shouldn't have happened"),
        }
    }
}
