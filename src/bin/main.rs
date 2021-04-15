use std::fs::File;
use std::io::Read;

use hyperfr::{address::Addresses, address::Address, HvMemoryFlags, bindgen as b};
use memmap::MmapOptions;

fn main() {
    let mut vm = hyperfr::HfVm::new().unwrap();
    let mut args = std::env::args_os();
    let image = args.nth(1).unwrap();
    let mut file = File::open(&image).unwrap();

    let addresses = Addresses::new();
    let mut map = MmapOptions::new().len(file.metadata().unwrap().len() as usize).map_anon().unwrap();
    file.read_exact(map.as_mut()).unwrap();

    let host_addr = Address::from(map.as_ptr());
    assert!(addresses.is_aligned(host_addr));

    vm.map_memory(host_addr, Address::new_from_usize(0x8000), map.len(), HvMemoryFlags::ALL).unwrap();
}