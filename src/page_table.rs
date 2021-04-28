// DS field should be equal to 0 for simplicity as we seem to have only 36 bits of address anyway.
// DS field is used when larger addresses.

// We also can have only 1 translation table

/*
A System register bit enables the stage of address translation, SCTLR_ELx.M or HCR_EL2.VM.
SCTLR_ELx.M:
  0 - EL1&0 stage 1 address translation disabled
  1 - EL1&0 stage 1 address translation enabled.
- Also need to consider bit I:
  - Stage 1 instruction access Cacheability control, for accesses at EL0 and EL1:

A System register bit determines the endianness of the translation table lookups, SCTLR_ELx.EE.
- we don't care, little-endian is default

A Translation Control Register (TCR_ELx) controls the stage of address translation.
- TG0
  Granule size - super important
  0b00 4KB
  0b01 64KB
  0b10 16KB
- IPS, bits [34:32]
  Intermediate Physical Address Size.
  0b000 32 bits, 4GB.
  0b001 36 bits, 64GB.  - This is our case
  0b010 40 bits, 1TB.
  0b011 42 bits, 4TB.
  0b100 44 bits, 16TB.
  0b101 48 bits, 256TB.
  0b110 52 bits, 4PB.

- T0SZ - the most important 6 bits -
  The maximum and minimum possible values for T0SZ depend on the level of translation table and the memory
  translation granule size, as described in the AArch64 Virtual Memory System Architecture chapter.

Physical address size is 36 bits.
But we can setup translation tables to have more than 36 bits!
Let's do that at a later stage.

FEAT_LPA is NOT implemented, as PA is not 4PB
FEAT_LVA IS implemented. I.e.
  VMSAv8-64 supports 52-bit VAs when using the 64KB translation granule.
  The size for other translation granules is not defined by this field.
FEAT_TTST = 1
  The maximum value of the TCR_ELx.{T0SZ,T1SZ} and VTCR_EL2.T0SZ fields is 48 for 4KB and 16KB granules,
  and 47 for 64KB granules.


TGran4:
  Supported, BUT LPA2 not implemented, so 4kb does not support 52 bits
TGran64:
  Not supported
TGran16:
  Supported, BUT LPA2 not implemented, so 16kb does not support 52 bits

TxSZ:
  Our effective minimum is 16.


The TCR_ELx.{SH0, ORGN0, IRGN0} fields define memory region attributes for the
translation table walks.


Let's consider an example.
Let's split our address into 11-11-11-14 bits

# These 36 bits are the ones I use.
0000_0000_000__1111_1111_111__1111_1111_111_____1111_1111_1111_11


inputsize = 36 # 64 - t0sz = 64 - 28
inputsize_max = 48
inputsize_min = 16
ps = 1 # 4 GB
reversedescriptors = False
update_AF = False
update_AP = False
grainsize = 14
firstblocklevel = 2
stride = 11
level = 2 # 4 - (1 + ((inputsize - grainsize - 1) // stride))


// See what that does. Those don't help getting set, but might be important.
descaddr.memattrs = WalkAttrDecode(TCR_EL1.SH0, TCR_EL1.ORGN0, TCR_EL1.IRGN0, secondstage);

outputsize = 36
baselowerbound = 14


addrselecttop = 35
addrselectbottom = 25



// For TTBR1 walk:
top = 55
inputsize = 36
inputsize_max = 48
inputsize_min = 16

*/

use crate::{GuestIpaAddress, GuestVaAddress, HvMemoryFlags};
use anyhow::bail;
use log::{debug, trace};

#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
struct TranslationTableDescriptor16k(u64);

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TranslationTableLevel3_16k {
    descriptors: [TranslationTableDescriptor16k; 2048],
}

impl Default for TranslationTableLevel3_16k {
    fn default() -> Self {
        Self {
            descriptors: [TranslationTableDescriptor16k::default(); 2048],
        }
    }
}

#[repr(C)]
pub struct TranslationTableLevel2_16k {
    descriptors: [TranslationTableDescriptor16k; 2048],
    level_3_tables: [TranslationTableLevel3_16k; 2048],
}

impl Default for TranslationTableLevel2_16k {
    fn default() -> Self {
        Self {
            descriptors: [TranslationTableDescriptor16k::default(); 2048],
            level_3_tables: [TranslationTableLevel3_16k::default(); 2048],
        }
    }
}

pub const fn bits(val: u64, start_inclusive: u64, end_inclusive: u64) -> u64 {
    let top_mask = match start_inclusive {
        63 => u64::MAX,
        0..=62 => (1u64 << (start_inclusive + 1)) - 1,
        _ => 0,
    };
    let bottom_mask = !((1 << end_inclusive) - 1);
    val & top_mask & bottom_mask
}

impl TranslationTableLevel2_16k {
    fn is_aligned(value: u64) -> bool {
        crate::aligner::ALIGNER_16K.is_aligned(value)
    }

    pub fn simulate_lookup(
        &self,
        table_start_ipa: crate::GuestIpaAddress,
        va: crate::GuestVaAddress,
    ) -> Option<GuestIpaAddress> {
        trace!(
            "simulate_lookup, table_start_ipa={:#x?}, va={:#x?}",
            table_start_ipa.0,
            va.0
        );
        let l2_idx = ((va.0 >> 25) & ((1 << 11) - 1)) as usize;
        let l2 = &self.descriptors[l2_idx];
        match l2.0 & 0b11 {
            // TABLE, points to L3 page
            0b11 => {
                let l3_ipa = l2.0 & ((1 << 48) - 1) & !((1 << 14) - 1);
                assert_eq!(l3_ipa, table_start_ipa.0 + self.get_t3_offset(l2_idx));

                let l3_idx = ((va.0 >> 14) & ((1 << 11) - 1)) as usize;
                let l3 = &self.level_3_tables[l2_idx as usize].descriptors[l3_idx as usize];

                if l3.0 & 0b11 != 0b11 {
                    return None;
                }

                let ipa = l3.0 & ((1 << 48) - 1) & !((1 << 14) - 1);
                Some(GuestIpaAddress(ipa + (va.0 & ((1 << 14) - 1))))
            }
            // BLOCK
            0b01 => {
                todo!("block l2 lookup not supported yet")
            }
            _ => None,
        }
    }

    // Get the offset from self's ptr into the L3 table for L2 table.
    fn get_t3_offset(&self, l2_idx: usize) -> u64 {
        let base = self as *const _ as u64;
        let l3_base = &self.level_3_tables as *const TranslationTableLevel3_16k;
        let l3 = unsafe { l3_base.add(l2_idx) };
        l3 as u64 - base
    }

    pub fn setup(
        &mut self,
        table_start_ipa: GuestIpaAddress,
        va: GuestVaAddress,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let va = va.0;
        let ipa = ipa.0;
        let table_start_ipa = table_start_ipa.0;

        let top_bit_set = (va >> 55) & 1 == 1;
        let size = size as u64;

        debug!("configuring translation tables table_start_ipa={:#x?}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}", table_start_ipa, va, ipa, size, flags);

        if !Self::is_aligned(table_start_ipa) {
            bail!(
                "table_start_ipa {:#x} is not aligned to page size",
                table_start_ipa
            )
        }
        if !Self::is_aligned(va) {
            bail!("va {:#x} is not aligned to page size", va)
        }
        if !Self::is_aligned(ipa) {
            bail!("ipa {:#x} is not aligned to page size", ipa)
        }
        if ipa + size >= crate::IPS_SIZE {
            bail!(
                "ipa {:#x?} / and or ipa + size are too large, does not fit into the TXSZ
                space which is limited by address {:#x?}",
                ipa,
                crate::IPS_SIZE - 1
            )
        }
        if !Self::is_aligned(size) {
            bail!("size {:#x} is not aligned to page size", size)
        }

        // Just a double-check for debugging
        // In pseudo-code this was:
        // if !IsZero(baseregister < 47: outputsize > ) -> throw AddressFault
        assert_eq!(bits(table_start_ipa, 47, 36), 0);

        if top_bit_set {
            // Make sure all bits <top:inputsize> are ones.
            // where inputsize = 64 - TxSZ and top=55
            assert_eq!(
                bits(va, 55, 64 - crate::TXSZ),
                bits(u64::MAX, 55, 64 - crate::TXSZ)
            )
        } else {
            // Make sure all bits up to TXSZ are zeroes.
            assert_eq!(bits(va, 55, 64 - crate::TXSZ), 0)
        }

        self._setup_internal(table_start_ipa, va, ipa, size, flags)
    }

    fn _setup_internal(
        &mut self,
        table_start_ipa: u64,
        mut va: u64,
        mut ipa: u64,
        mut size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        use crate::aligner::Aligner;
        const BLOCK_SIZE: u64 = 1 << 25;
        const BLOCK_SIZE_ALIGNER: Aligner = Aligner::new_from_mask(!((1 << 25) - 1));

        loop {
            if size == 0 {
                return Ok(());
            }

            if BLOCK_SIZE_ALIGNER.is_aligned(va) {
                while size >= BLOCK_SIZE {
                    self._setup_one_block(va, ipa, flags)?;
                    size -= BLOCK_SIZE;
                    va += BLOCK_SIZE;
                    ipa += BLOCK_SIZE;
                }
                if size > 0 {
                    return self._setup_internal_l3(table_start_ipa, va, ipa, size, flags);
                }
            } else {
                let next_block_start = BLOCK_SIZE_ALIGNER.align_up(va);
                let l3size = size.min(next_block_start - va);
                self._setup_internal_l3(table_start_ipa, va, ipa, l3size, flags)?;
                va += l3size;
                ipa += l3size;
                size -= l3size;
            }
        }
    }

    fn _setup_one_block(&mut self, va: u64, ipa: u64, flags: HvMemoryFlags) -> anyhow::Result<()> {
        let l2 = (va >> (14 + 11)) & ((1 << 11) - 1);
        let l2desc = &mut self.descriptors[l2 as usize];

        if l2desc.0 & 0b11 != 0 {
            bail!("L2 table {} already set-up", l2);
        }

        // Block
        l2desc.0 = 0b01;
        l2desc.0 |= 1 << 10; // AF=1
        l2desc.0 |= ipa & ((1 << 48) - 1) & !((1 << 26) - 1);

        l2desc.0 |= 0b10 << 8; // SH
        if !(flags.contains(HvMemoryFlags::HV_MEMORY_EXEC)) {
            l2desc.0 |= 1 << 53; // Privileged execute never
            l2desc.0 |= 1 << 54; // Unprivileged execute never
        }

        // AP bits AP[2:1], bits[7:6] Data Access Permissions bits, see Memory access control on page D5-2731.
        if !flags.contains(HvMemoryFlags::HV_MEMORY_WRITE) {
            l2desc.0 |= 0b10 << 6;
        }

        trace!(
            "l2 block: l2={}, l2val={:#x?}, va: {:#x?}, ipa: {:#x?}, flags: {:?}",
            l2,
            l2desc.0,
            va,
            ipa,
            flags
        );
        Ok(())
    }

    fn _setup_internal_l3(
        &mut self,
        table_start_ipa: u64,
        va: u64,
        ipa: u64,
        size: u64,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let mut ipa = ipa;
        let mut va = va;
        let ipa_end = ipa + size;
        let page = crate::VA_PAGE;

        // an impossible value
        let mut prev_l2_idx = 2048;

        while ipa < ipa_end {
            // to get l2 idx, get bits (35:25)
            let l2_idx = (va >> (14 + 11)) & ((1 << 11) - 1);

            if l2_idx != prev_l2_idx {
                let offset = self.get_t3_offset(l2_idx as usize);
                let l2_desc = &mut self.descriptors[l2_idx as usize];

                let l3_offset = table_start_ipa + offset;
                assert_eq!(bits(l3_offset, 47, 14), l3_offset);

                let new_value = 0b11 | (table_start_ipa + offset);

                match l2_desc.0 & 0b11 {
                    0b01 => bail!("l2={} was previously already configured as a block", l2_idx),
                    0b11 => {
                        // The table was previously configured. Make sure the value is the same.
                        if l2_desc.0 != new_value {
                            bail!("l2={} was previously configured with value {:#x?}, wanted to write {:#x?}", l2_idx, l2_desc.0, new_value)
                        }
                    }
                    _ => {
                        l2_desc.0 = new_value;
                        trace!(
                            "l2 table: va={:#x?}, ttbr: l2_idx={}, l2_val={:#x?}",
                            va,
                            l2_idx,
                            new_value,
                        );
                    }
                }
            }
            prev_l2_idx = l2_idx;

            let l3_idx = (va >> 14) & ((1 << 11) - 1);
            let l3_desc = &mut self.level_3_tables[l2_idx as usize].descriptors[l3_idx as usize];

            if l3_desc.0 & 0b11 > 0 {
                bail!(
                    "page l2={},l3={} was already configured previously",
                    l2_idx,
                    l3_idx
                );
            }

            let mut v: u64 = 0b11;
            v |= 1 << 10; // AF=1
            v |= 0b10 << 8; // SH
            v |= ipa;

            if !(flags.contains(HvMemoryFlags::HV_MEMORY_EXEC)) {
                v |= 1 << 53; // Privileged execute never
            }

            // AP bits AP[2:1], bits[7:6] Data Access Permissions bits, see Memory access control on page D5-2731.
            if !flags.contains(HvMemoryFlags::HV_MEMORY_WRITE) {
                v |= 0b10 << 6;
            }

            l3_desc.0 = v;

            trace!(
                "l3 table: va={:#x?}, ttbr: l2_idx={}, l3_idx={}, l3val={:#x?}",
                va,
                l2_idx,
                l3_idx,
                v
            );

            va += page;
            ipa += page;
        }
        Ok(())
    }
}
