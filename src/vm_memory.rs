use std::cell::UnsafeCell;

use anyhow::{anyhow, bail};

use crate::{
    addresses::{GuestIpaAddress, Offset},
    error::{Error, Kind},
};

#[derive(Debug)]
pub struct GuestMemoryMmap {
    start_addr: GuestIpaAddress,
    size: usize,
    map: UnsafeCell<memmap::MmapMut>,
}

unsafe impl Send for GuestMemoryMmap {}
unsafe impl Sync for GuestMemoryMmap {}

impl GuestMemoryMmap {
    pub fn new(start_addr: GuestIpaAddress, size: usize) -> crate::error::Result<Self> {
        let map = memmap::MmapOptions::default()
            .len(size)
            .map_anon()
            .map_err(|e| Error::from_kind(Kind::Mmap(e)))?;
        Ok(Self {
            start_addr,
            size,
            map: UnsafeCell::new(map),
        })
    }

    pub fn get_offset_from_start(&self, addr: GuestIpaAddress) -> crate::error::Result<Offset> {
        if addr.0 < self.start_addr.0 {
            return Err(Error::from_kind(Kind::InvalidGuestIpaAddress(addr)));
        }
        Ok(Offset(addr.0 - self.start_addr.0))
    }

    #[inline(never)]
    pub fn get_slice(&self, addr: GuestIpaAddress, size: usize) -> crate::error::Result<&mut [u8]> {
        let offset = self.get_offset_from_start(addr)?.0 as usize;
        let map = unsafe { &mut *self.map.get() };
        Ok(map
            .get_mut(offset..(offset + size))
            .ok_or_else(|| Kind::InvalidGuestMemorySlice { ipa: addr, size })?)
    }
}
