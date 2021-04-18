struct GranulePermissions {}
struct ResolvedAddress {
    addr: u64,
}
struct ResolutionError {}

struct Aarch64TranslationTableEntry {
    data: u64,
}

struct EntryBlock16k {
    data: u64
}
struct EntryTable16k {
    data: u64
}

impl EntryBlock16k {
    pub fn output_address(&self) -> u64 {
        (self.data >> 25) & ((1 << 24) - 1)
    }
}

impl EntryTable16k {
    pub fn next_address(&self) -> u64 {
        (self.data >> 14) & ((1 << 35) - 1)
    }
}

enum TableEntry16k {
    Block(EntryBlock16k),
    Table(EntryTable16k)
}

impl Aarch64TranslationTableEntry {
    fn is_valid(&self) -> bool {
        self.data & 1 == 1
    }
    fn get(&self) -> Option<TableEntry> {
        if self.is_valid() {
            if (self.data >> 1) & 1 == 0 {
                Some(EntryBlock{data: self.data})
            } else {
                Some(EntryTable{data: self.data})
            }
        } else {
            None
        }
    }
}

struct Aarch64TranslationTableLevel16kLevel<const N: usize> {
    entries: [Aarch64TranslationTableEntry; N]
}

impl<const N: usize> Aarch64TranslationTableLevel16kLevel<N> {
    fn resolve(&self, addr: u64, level: u8) -> Result<ResolvedAddress, ResolutionError> {
        let index = match level {
            0 => {
                ((addr >> 47) & 0b11111) as usize
            },
            1 => {
                ((addr >> 36) & 0b111_1111_1111) as usize
            },
            2 => {
                ((addr >> 25) & 0b111_1111_1111) as usize
            },
            3 => {
                ((addr >> 14) & 0b111_1111_1111) as usize
            },
            _ => panic!("unsupported translation level {}", level)
        };
        let entry = &self.entries[index];
        if !entry.is_present() {
            return Err(ResolutionError{})
        }
        if entry.is_final() {
            return Ok(ResolvedAddress{
                addr,
            })
        };
        match entry.get_next_address() {
            Some(next) => {
                let idx = next.checked_sub(dram_offset).unwrap();
            },
            None => {
                return Err(ResolutionError{})
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn vm_memory() {
        use std::sync::Arc;
        pub const DRAM_MEM_START: usize = 0x8000_0000; // 2 GB.
        // This is bad, but seems to fuck up without a page table if set to higher, as the executable is not a PIE one.
        pub const EXEC_START: usize = 0; // 512 MB

        pub const MEM_SIZE: usize = 32 * 1024 * 1024;

        use vm_memory::{Address, GuestMemory};
        let mmap_region = vm_memory::MmapRegion::new(MEM_SIZE).unwrap();
        let guest_mem = vm_memory::GuestMemoryMmap::new();
        let guest_base = vm_memory::GuestAddress::new(DRAM_MEM_START as u64);

        let guest_region = Arc::new(vm_memory::GuestRegionMmap::new(mmap_region, guest_base).unwrap());
        let guest_mem = guest_mem.insert_region(guest_region).unwrap();

        guest_mem.with_regions(|idx, region| {
            region.as_ptr()
        });
    }

}

// What do we want to do with it?
// take 11 bits, take 11 bits, take 11 bits