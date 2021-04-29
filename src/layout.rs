use crate::addresses::*;

// Memory structure:
// VA_START - the virtual memory of the kernel so that it's in TTBR1.
// At that address we load the kernel itself, including exception vector table.
// VA_START + 1GB = DRAM

pub const DRAM_IPA_START: GuestIpaAddress = GuestIpaAddress(0x80_0000);
pub const VA_START: GuestVaAddress = GuestVaAddress(0xffff_fff0_0000_0000);
pub const DRAM_VA_START: GuestVaAddress = VA_START.add(Offset(DRAM_IPA_START.0));

// this could be configurable, it's just that we don't care yet.
// This is 32 MiB, we just don't need more.
pub const MEMORY_SIZE: usize = 128 * 1024 * 1024;

pub const STACK_SIZE: u64 = 1024 * 1024;

pub const TCR_EL1_IPS: u64 = 0b001 << 32; // 64 GB
pub const TCR_EL1_HA: u64 = 1 << 39;
pub const TCR_EL1_HD: u64 = 1 << 40;
