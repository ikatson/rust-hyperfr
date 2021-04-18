use std::fs::File;
use std::io::Read;

use hyperfr::{bindgen as b, HvMemoryFlags};
use memmap::MmapOptions;

pub const DRAM_MEM_START: usize = 0x8000_0000; // 2 GB.
                                               // This is bad, but seems to fuck up without a page table if set to higher, as the executable is not a PIE one.
pub const EXEC_START: usize = 0; // 512 MB,
pub const MAPPED_IO_START: u64 = 1 << 30; // 1 GB
pub const MEM_SIZE: usize = 32 * 1024 * 1024;

fn main() {
    let mut vm = hyperfr::HfVm::new().unwrap();
    let mut args = std::env::args_os();
    let image = args.nth(1).unwrap();

    let elf = vm.load_elf(&image).unwrap();
    let memory = vm.get_memory();

    let vcpu = vm.vcpu_create_and_run(memory, elf.entrypoint, move |res| {
        // println!("{:#x?}", res);
        // let stack_end = 1024 * 1024usize;
        // let stack_start = stack_end - 80;
        // let stack = &map[stack_start..stack_end];
        // hexdump::hexdump(stack);
        Ok(())
    });
    vcpu.join().unwrap();
}
