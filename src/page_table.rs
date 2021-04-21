use vm_memory::GuestAddress;

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
*/

use crate::HvMemoryFlags;
use anyhow::bail;
use log::debug;

#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
struct TranslationTableDescriptor16k(u64);

impl TranslationTableDescriptor16k {
    fn new(base_address: GuestAddress) -> Self {
        let mut value = 0u64;
        value |= 0b11; // valid + table bits

        // Bits 47:14 included
        assert_eq!(base_address.0 & !((1 << 14) - 1), base_address.0);

        value |= base_address.0;
        Self(value)
    }
}

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

// impl TranslationTable16kAllocator {
//     pub fn allocate_recursive_identity_block(
//         base_address: GuestAddress,
//     ) -> TranslationTableLevel16k {
//         let copy = TranslationTableDescriptor16k::new(base_address);
//         let mut table = TranslationTableLevel16k {
//             entries: [copy; 2048],
//         };
//         // each entry in the level 3 table should be identity.
//         // i.e. 0x0000_0000_
//         for descr in table.entries.iter_mut() {
//             // descr.0
//         }
//         unimplemented!()
//     }
// }

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

impl TranslationTableLevel2_16k {
    fn is_aligned(value: u64) -> bool {
        value & ((1 << 14) - 1) == 0
    }
    fn get_t3_offset(&self, n: usize) -> u64 {
        let base = core::mem::size_of_val(&self.descriptors);
        (base + (n * 2048 * 8)) as u64
    }

    pub fn setup(
        &mut self,
        table_start_ipa: u64,
        va: GuestAddress,
        ipa: u64,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let top_bit_set = (va.0 >> 55) & 1 == 1;
        let size = size as u64;

        debug!("configuring translation tables table_start_ipa={:#x?}, va={:#x?}, ipa={:#x?}, size={}, flags={:?}", table_start_ipa, va.0, ipa, size, flags);

        if !Self::is_aligned(table_start_ipa) {
            bail!(
                "table_start_ipa {:#x} is not aligned to page size",
                table_start_ipa
            )
        }
        if !Self::is_aligned(va.0) {
            bail!("va {:#x} is not aligned to page size", va.0)
        }
        if !Self::is_aligned(ipa) {
            bail!("ipa {:#x} is not aligned to page size", ipa)
        }
        if !Self::is_aligned(size) {
            bail!("size {:#x} is not aligned to page size", size)
        }
        if top_bit_set {
            assert_eq!(va.0 >> (64 - crate::TXSZ), (1 << crate::TXSZ) - 1)
        } else {
            assert_eq!(va.0 >> (64 - crate::TXSZ), 0)
        }

        let va_bottom = va.0 & ((1 << crate::TXSZ) - 1);

        let l2_range = va_bottom >> (14 + 11);
        for l2 in 0..=(l2_range as usize) {
            let t3offset = self.get_t3_offset(l2);
            let l2desc = &mut self.descriptors[l2];
            l2desc.0 |= 0b11;
            l2desc.0 |= table_start_ipa + t3offset;

            let l2_ipa_base: u64 = ipa + ((l2 as u64) << (14 + 11));

            for (l3, l3desc) in self.level_3_tables[l2].descriptors.iter_mut().enumerate() {
                let page_ipa = l2_ipa_base + ((l3 as u64) << 14);
                l3desc.0 |= 0b11;
                l3desc.0 |= page_ipa;

                // set access flag, otherwise it causes faults that we don't handle.
                l3desc.0 |= 1 << 10; // AF=1;

                // Not sure what this means, but shareable sounds good?
                l3desc.0 |= 0b10 << 8; // SH

                // We set up MAIR_EL1 to say that index 0 is our main memory.
                // l3desc.0 = 0b___ << 2; // AttrIndx

                println!(
                    "ttbr: l2={}, l3={}, l2val={:#x?}, l3val={:#x?}",
                    l2, l3, l2desc.0, l3desc.0
                );
            }
        }
        Ok(())
    }
}

pub unsafe fn identity_map_36_bits_of_memory(
    ptr: *mut TranslationTableLevel2_16k,
    ttbr: GuestAddress,
) -> anyhow::Result<()> {
    let offset = ttbr.0;
    let table = &mut *ptr as &mut TranslationTableLevel2_16k;
    for l2 in 0..2048usize {
        let t3offset = table.get_t3_offset(l2) as u64;
        let l2desc = &mut table.descriptors[l2];
        l2desc.0 |= 0b11;
        l2desc.0 |= offset + t3offset;

        let va = (l2 as u64) << 25;
        for (l3, l3desc) in table.level_3_tables[l2].descriptors.iter_mut().enumerate() {
            l3desc.0 |= 0b11;
            l3desc.0 |= va | ((l3 as u64) << 14);

            // set access flag, otherwise it causes faults that we don't handle.
            l3desc.0 |= 1 << 10; // AF=1;

            // Not sure what this means, but shareable sounds good?
            l3desc.0 |= 0b10 << 8; // SH

            // We set up MAIR_EL1 to say that index 0 is our main memory.
            // l3desc.0 = 0b___ << 2; // AttrIndx

            // println!("{}, {}, {:x?}, {:x?}", l2, l3, l2desc.0, l3desc.0);
        }
    }
    Ok(())
}
