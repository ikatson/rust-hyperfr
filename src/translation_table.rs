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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum Aarch64TranslationGranule {
    P4k,
    P16k,
    P64k,
}

impl Aarch64TranslationGranule {
    pub const fn tg0_bits(&self) -> u64 {
        match self {
            Aarch64TranslationGranule::P4k => 0,
            Aarch64TranslationGranule::P16k => 0b10 << 14,
            Aarch64TranslationGranule::P64k => 0b01 << 14,
        }
    }
    pub const fn tg1_bits(&self) -> u64 {
        match self {
            Aarch64TranslationGranule::P4k => 0b10 << 30,
            Aarch64TranslationGranule::P16k => 0b01 << 30,
            Aarch64TranslationGranule::P64k => 0b11 << 30,
        }
    }
    pub const fn page_size_bits(&self) -> u8 {
        match self {
            Aarch64TranslationGranule::P4k => 12,
            Aarch64TranslationGranule::P16k => 14,
            Aarch64TranslationGranule::P64k => 16,
        }
    }
    pub const fn page_size(&self) -> u64 {
        1 << self.page_size_bits()
    }

    pub const fn aligner(&self) -> Aligner {
        let mask = !(self.page_size() - 1);
        Aligner::new_from_mask(mask)
    }

    pub const fn layout_for_level(&self, level: i8, txsz: u8) -> Layout {
        let (bt, bl) = self.bits_range(level, txsz);
        let stride = bt - bl + 1;
        let size = core::mem::size_of::<Descriptor>() * (1 << stride);
        let align = 1 << self.page_size_bits();
        unsafe { Layout::from_size_align_unchecked(size, align) }
    }

    pub const fn initial_level(&self, txsz: u8) -> i8 {
        match self {
            Aarch64TranslationGranule::P4k => match txsz {
                12..=15 => -1,
                16..=24 => 0,
                25..=33 => 1,
                34..=42 => 2,
                43..=48 => 3,
                _ => i8::MIN,
            },
            Aarch64TranslationGranule::P16k => match txsz {
                12..=16 => 0,
                17..=27 => 1,
                28..=38 => 2,
                39..=48 => 3,
                _ => i8::MIN,
            },
            Aarch64TranslationGranule::P64k => match txsz {
                12..=21 => 1,
                22..=34 => 2,
                35..=47 => 3,
                _ => i8::MIN,
            },
        }
    }

    pub const fn block_size_bits(&self, table_level: i8) -> Option<u8> {
        match self {
            Aarch64TranslationGranule::P4k => match table_level {
                2 => Some(21),
                1 => Some(30),
                _ => None,
            },
            Aarch64TranslationGranule::P16k => match table_level {
                2 => Some(25),
                _ => None,
            },
            Aarch64TranslationGranule::P64k => match table_level {
                2 => Some(29),
                _ => None,
            },
        }
    }

    pub const fn block_size(&self, table_level: i8) -> Option<u64> {
        // Can't use map in const fn.
        match self.block_size_bits(table_level) {
            Some(b) => Some(1 << b),
            None => None,
        }
    }

    pub const fn max_stride(&self) -> u8 {
        self.page_size_bits() - 3
    }

    pub const fn bits_range(&self, table_level: i8, txsz: u8) -> (u8, u8) {
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

struct Descriptor(u64);

#[derive(Copy, Clone, Debug)]
struct TableMetadata {
    start: GuestIpaAddress,
    level: i8,
    descriptors: *mut Descriptor,
}

impl TableMetadata {
    fn descriptor(&self, idx: usize) -> &Descriptor {
        unsafe { &*(self.descriptors.add(idx)) }
    }

    fn descriptor_mut(&mut self, idx: usize) -> &mut Descriptor {
        unsafe { &mut *(self.descriptors.add(idx)) }
    }
}

pub trait TTMgr: core::fmt::Debug + Send + Sync {
    fn get_granule(&self) -> Aarch64TranslationGranule;
    fn get_txsz(&self) -> u8;
    fn setup(
        &self,
        memory_mgr: &mut GuestMemoryManager,
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
    fn get_top_ttbr_layout(&self) -> anyhow::Result<Layout>;
}

impl<const G: Aarch64TranslationGranule, const TXSZ: u8> TTMgr
    for TranslationTableManager<G, TXSZ>
{
    fn get_granule(&self) -> Aarch64TranslationGranule {
        Self::get_granule(&self)
    }

    fn get_txsz(&self) -> u8 {
        Self::get_txsz(&self)
    }

    fn setup(
        &self,
        memory_mgr: &mut GuestMemoryManager,
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
    fn get_top_ttbr_layout(&self) -> anyhow::Result<Layout> {
        Self::get_top_ttbr_layout(&self)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TranslationTableManager<const G: Aarch64TranslationGranule, const TXSZ: u8> {
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
    ips_size: u64,
    ips_bits: u8,
}

pub fn new_ttbr_mgr(
    granule: Aarch64TranslationGranule,
    txsz: u8,
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
) -> anyhow::Result<Box<dyn TTMgr>> {
    use Aarch64TranslationGranule::*;
    match (granule, txsz) {
        (P16k, 28) => Ok(Box::new(TranslationTableManager::<{ P16k }, 28>::new(
            ttbr0, ttbr1,
        )?)),
        _ => bail!(
            "unsupported granule/txsz combination: {:?}/{}",
            granule,
            txsz
        ),
    }
}

impl<const G: Aarch64TranslationGranule, const TXSZ: u8> TranslationTableManager<G, TXSZ> {
    fn new(ttbr0: GuestIpaAddress, ttbr1: GuestIpaAddress) -> anyhow::Result<Self> {
        let ips_bits = 36;
        let ips_size = 1 << ips_bits;
        Ok(Self {
            ttbr0,
            ttbr1,
            ips_size,
            ips_bits,
        })
    }

    fn initial_level(&self) -> i8 {
        G.initial_level(TXSZ)
    }

    fn layout_for_level(&self, level: i8) -> Layout {
        G.layout_for_level(level, TXSZ)
    }

    pub fn get_granule(&self) -> Aarch64TranslationGranule {
        G
    }

    pub fn get_txsz(&self) -> u8 {
        TXSZ
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
        assert_eq!(bits(ipa.0, 47, self.ips_bits), 0);

        if top_bit {
            // Make sure all bits <top:inputsize> are ones.
            // where inputsize = 64 - TxSZ and top=55
            assert_eq!(
                bits(va.0, 55, 64 - TXSZ),
                bits(u64::MAX, 55, 64 - TXSZ),
                "bits [64:{}] should be 1, but they are not in {:?}",
                (64 - TXSZ),
                va
            )
        } else {
            // Make sure all bits up to TXSZ are zeroes.
            assert_eq!(
                bits(va.0, 55, 64 - TXSZ),
                0,
                "bits [64:{}] should be zeroes, but they are not in {:?}",
                (64 - TXSZ),
                va
            )
        }

        self.get_ttbr_at(memory_mgr, ipa)
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

        let aligner = G.aligner();
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
            let (bt, bb) = G.bits_range(table.level, TXSZ);
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
                    let psb = G.page_size_bits();
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
                    let block_size_bits = match G.block_size_bits(table.level) {
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
        memory_mgr: &mut GuestMemoryManager,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        debug_assert!(G.aligner().is_aligned(va.0));
        debug_assert!(G.aligner().is_aligned(ipa.0));
        debug_assert!(size > 0);
        debug_assert!(G.aligner().is_aligned(size as u64));

        let (bt, bl) = G.bits_range(table.level, TXSZ);

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

    #[allow(clippy::too_many_arguments)]
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
        debug_assert!(G.aligner().is_aligned(va.0));
        debug_assert!(G.aligner().is_aligned(ipa.0));
        debug_assert!(size > 0);
        debug_assert!(G.aligner().is_aligned(size as u64));

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

        if let Some(block_size) = G.block_size(table.level) {
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
                let ipa = bits(descriptor.0, 47, G.page_size_bits());
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
