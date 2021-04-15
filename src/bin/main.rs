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
    let file_len = file.metadata().unwrap().len() as usize;
    let aligned_len = addresses.next_aligned(Address::new_from_usize(file_len)).as_usize();

    let mut map = MmapOptions::new().len(aligned_len).map_anon().unwrap();
    file.read_exact(&mut map.as_mut()[..file_len]).unwrap();

    let host_addr = Address::from(map.as_ptr());
    assert!(addresses.is_aligned(host_addr));

    let guest_addr = 0x8000;

    vm.map_memory(host_addr, Address::new_from_usize(guest_addr), map.len(), HvMemoryFlags::ALL).unwrap();

    let vcpu = vm.vcpu_create_and_run(|res| {
        dbg!(res);
        Ok(())
    });
    vcpu.join().unwrap();
}