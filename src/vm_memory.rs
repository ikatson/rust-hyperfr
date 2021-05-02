use std::cell::UnsafeCell;

use anyhow::{anyhow, bail};

use crate::addresses::{GuestIpaAddress, Offset};

#[derive(Debug)]
pub struct GuestMemoryMmap {
    start_addr: GuestIpaAddress,
    size: usize,
    map: UnsafeCell<memmap::MmapMut>,
}

unsafe impl Send for GuestMemoryMmap {}
unsafe impl Sync for GuestMemoryMmap {}

impl GuestMemoryMmap {
    pub fn new(start_addr: GuestIpaAddress, size: usize) -> anyhow::Result<Self> {
        let map = memmap::MmapOptions::default()
            .len(size)
            .map_anon()?
            .make_exec()?
            .make_mut()?;
        Ok(Self {
            start_addr,
            size,
            map: UnsafeCell::new(map),
        })
    }

    pub fn get_offset_from_start(&self, addr: GuestIpaAddress) -> anyhow::Result<Offset> {
        if addr.0 < self.start_addr.0 {
            bail!(
                "addr should be >= than start_addr, but {:?} < {:?}",
                addr,
                self.start_addr
            )
        }
        Ok(Offset(addr.0 - self.start_addr.0))
    }

    pub fn get_slice(&self, addr: GuestIpaAddress, size: usize) -> anyhow::Result<&mut [u8]> {
        let offset = self.get_offset_from_start(addr)?.0 as usize;
        let map = unsafe { &mut *self.map.get() };
        map.get_mut(offset..(offset + size))
            .ok_or_else(|| anyhow!("can't get slice at {:?} of size {:?} - out of bounds"))
    }
}
