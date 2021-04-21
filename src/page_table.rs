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

1111_1111_111__1111_1111_111__1111_1111_111_____1111_1111_1111_11

If I want to set up an identity mapping:
- All of these should be block entries, not table entries.
  Each block entry:
  - Says it's a block
  - Has a pointer to the next table base address

Theoretically I could setup a recursive block, that:
- says it's a block
- loops into itself

1. That should be the simplest translation table possible.
So let's implement that one first.

// DEBUG:
- maybe set NFD0? Not sure.
- maybe EPD0?


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

pub struct TranslationTable16kAllocator {}

#[derive(Clone, Copy, Debug)]
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

#[derive(Debug)]
pub struct TranslationTableLevel16k {
    entries: [TranslationTableDescriptor16k; 2048],
}

impl TranslationTable16kAllocator {
    pub fn allocate_recursive_identity_block(
        base_address: GuestAddress,
    ) -> TranslationTableLevel16k {
        let copy = TranslationTableDescriptor16k::new(base_address);
        // let copy = TranslationTableDescriptor16k(0);
        TranslationTableLevel16k {
            entries: [copy; 2048],
        }
    }
}
