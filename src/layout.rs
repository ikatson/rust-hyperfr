use crate::addresses::*;
use crate::page_table;

// Memory structure:
// VA_START - the virtual memory of the kernel so that it's in TTBR1.
// At that address we load the kernel itself, including exception vector table.
// VA_START + 1GB = DRAM

pub const VA_PAGE: u64 = 1 << 14;

pub const DRAM_IPA_START: GuestIpaAddress = GuestIpaAddress(0x80_0000);
pub const VA_START: GuestVaAddress = GuestVaAddress(0xffff_fff0_0000_0000);
pub const DRAM_VA_START: GuestVaAddress = VA_START.add(Offset(DRAM_IPA_START.0));

pub const TTBR_SIZE: usize = core::mem::size_of::<page_table::TranslationTableLevel2_16k>();

// this could be configurable, it's just that we don't care yet.
// This is 32 MiB, we just don't need more.
pub const MEMORY_SIZE: usize = 128 * 1024 * 1024;

pub const STACK_SIZE: u64 = 1024 * 1024;
pub const STACK_END: GuestVaAddress = DRAM_VA_START.add(Offset(MEMORY_SIZE as u64));

pub const TXSZ: u64 = 28;
pub const IPS_SIZE: u64 = 1 << 36; // 64 GB address size

pub const TCR_EL1_TG0_GRANULE: u64 = 0b10 << 14;
pub const TCR_EL1_TG1_GRANULE: u64 = 0b01 << 30;
pub const TCR_EL1_IPS: u64 = 0b001 << 32; // 64 GB
pub const TCR_EL1_T0SZ: u64 = TXSZ; // so that 36 bits remains.
pub const TCR_EL1_T1SZ: u64 = TXSZ << 16;
pub const TCR_EL1_HA: u64 = 1 << 39;
pub const TCR_EL1_HD: u64 = 1 << 40;
