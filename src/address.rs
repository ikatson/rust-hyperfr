use std::ops::Add;

fn get_page_size() -> usize {
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    page as usize
}

#[derive(Copy, Clone, Debug)]
pub struct Addresses {
    page_size: usize,
}

pub fn is_multiple_of_two(mut value: usize) -> bool {
    while value > 1 {
        if value & 1 == 1 {
            return false;
        }
        value >>= 1;
    }
    true
}

impl Addresses {
    pub fn new() -> Self {
        let page_size = get_page_size();
        assert!(is_multiple_of_two(page_size));
        Self { page_size }
    }

    pub fn get_page_size(&self) -> usize {
        self.page_size
    }

    pub fn address(&self, addr: usize, align: bool) -> Address {
        let addr = Address(addr);
        if align {
            self.align(addr)
        } else {
            addr
        }
    }

    pub fn next_aligned(&self, address: Address) -> Address {
        if self.is_aligned(address) {
            return address;
        }
        self.align(Address(address.0 + self.page_size))
    }

    pub fn align(&self, address: Address) -> Address {
        Address(address.0 & !(self.page_size - 1))
    }

    pub fn is_aligned(&self, address: Address) -> bool {
        self.align(address) == address
    }
}

impl Default for Addresses {
    fn default() -> Self {
        Addresses::new()
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Address(usize);

impl Address {
    pub fn new_from_usize(addr: usize) -> Self {
        Self(addr)
    }
    pub fn as_usize(&self) -> usize {
        self.0
    }
}

impl<T> From<*const T> for Address {
    fn from(ptr: *const T) -> Self {
        Self(ptr as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_multiple_of_two() {
        for i in 0b10..=0b10000000000000 {
            match i {
                0b10 | 0b100 | 0b1000 | 0b10000 | 0b100000 | 0b1000000 | 0b10000000
                | 0b100000000 | 0b1000000000 | 0b10000000000 | 0b100000000000 | 0b1000000000000
                | 0b10000000000000 => assert_eq!(
                    is_multiple_of_two(i),
                    true,
                    "{} was expected to be a multiple of two",
                    i
                ),
                _ => assert_eq!(
                    is_multiple_of_two(i),
                    false,
                    "{} was not expected to be a multiple of two",
                    i
                ),
            }
        }
    }

    #[test]
    fn test_get_page_size() {
        assert_eq!(get_page_size(), 16384);
    }

    #[test]
    fn test_address_align() {
        let addrs = Addresses::new();
        assert_eq!(addrs.address(16385, true).as_usize(), 16384)
    }

    #[test]
    fn test_is_aligned() {
        let addrs = Addresses::new();
        assert_eq!(addrs.is_aligned(Address::new_from_usize(16385)), false);
        assert_eq!(addrs.is_aligned(Address::new_from_usize(16384)), true);
    }
}
