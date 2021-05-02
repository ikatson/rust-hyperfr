pub type Result<T> = core::result::Result<T, Error>;

pub mod smallvec {
    use std::mem::MaybeUninit;

    #[derive(Debug)]
    pub struct SmallVec<T, const S: usize> {
        items: [MaybeUninit<T>; S],
        start: usize,
        length: usize,
    }

    impl<T, const S: usize> SmallVec<T, S> {
        pub fn get(&self, idx: usize) -> Option<&T> {
            if idx >= self.length {
                return None;
            }
            let mut true_idx = self.start + idx;
            if true_idx >= S {
                // wrap around
                true_idx -= S;
            };
            return Some(unsafe { &*self.items[true_idx].as_ptr() });
        }

        pub fn iter(&self) -> impl DoubleEndedIterator<Item = &T> {
            SmallVecIterator {
                v: self,
                start_consumed: 0,
                end_consumed: 0,
            }
        }
    }

    struct SmallVecIterator<'a, T, const S: usize> {
        v: &'a SmallVec<T, S>,
        start_consumed: usize,
        end_consumed: usize,
    }

    impl<'a, T, const S: usize> Iterator for SmallVecIterator<'a, T, S> {
        type Item = &'a T;
        fn next(&mut self) -> Option<Self::Item> {
            let remaining = self.v.length - self.end_consumed - self.start_consumed;
            if remaining > 0 {
                let item = self.v.get(self.start_consumed).unwrap();
                self.start_consumed += 1;
                Some(item)
            } else {
                None
            }
        }
    }

    impl<'a, T, const S: usize> DoubleEndedIterator for SmallVecIterator<'a, T, S> {
        fn next_back(&mut self) -> Option<Self::Item> {
            let remaining = self.v.length - self.end_consumed - self.start_consumed;
            if remaining > 0 {
                let idx = self.v.length - 1 - self.end_consumed;
                let item = self.v.get(idx).unwrap();
                self.end_consumed += 1;
                Some(item)
            } else {
                None
            }
        }
    }

    impl<T: Sized, const S: usize> SmallVec<T, S> {
        pub fn new() -> Self {
            Self {
                items: unsafe { MaybeUninit::uninit().assume_init() },
                start: 0,
                length: 0,
            }
        }
        pub fn push_wrapping(&mut self, item: T) {
            if self.length < S {
                // not yet wrapped
                unsafe {
                    self.items[self.start + self.length]
                        .as_mut_ptr()
                        .write(item)
                };
                self.length += 1;
                return;
            }
            // length is equal to S
            unsafe { self.items[self.start].as_mut_ptr().write(item) };
            self.start += 1;
        }
    }
}

use std::borrow::Cow;

use smallvec::SmallVec;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress},
    translation_table::Aarch64TranslationGranule,
};

#[derive(Debug)]
pub enum Kind {
    ProgrammingError(Cow<'static, str>),
    Mmap(std::io::Error),
    InvalidGuestIpaAddress(GuestIpaAddress),
    InvalidGuestMemorySlice {
        ipa: GuestIpaAddress,
        size: usize,
    },
    GranuleTxszNotSupported {
        granule: Aarch64TranslationGranule,
        txsz: u8,
    },
    TopBitsShouldBeOne {
        top: u8,
        va: GuestVaAddress,
    },
    TopBitsShouldBeZero {
        top: u8,
        va: GuestVaAddress,
    },
    NotAligned {
        value: u64,
        name: &'static str,
    },
    IpaDoesNotFitIps {
        ipa: GuestIpaAddress,
        ips_limit: GuestIpaAddress,
    },
    IpaPlusSizeOverflow {
        ipa: GuestIpaAddress,
        size: usize,
    },
    NotAPowerOfTwo {
        value: u64,
    },
    HvReturnTUnrecognized {
        value: crate::bindgen::hv_return_t,
        function_name: &'static str,
    },
    HvReturnTNotSuccess {
        value: crate::bindgen_util::HVReturnT,
        function_name: &'static str,
    },
}

impl core::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Mmap(e) => f.write_fmt(format_args!("error doing mmap: {}", e)),
            Kind::InvalidGuestIpaAddress(addr) => {
                f.write_fmt(format_args!("invalid guest address: {:?}", addr))
            }
            Kind::InvalidGuestMemorySlice { ipa, size } => f.write_fmt(format_args!(
                "invalid guest memory slice (out of bounds): ipa {:?}, size {}",
                ipa, size
            )),
            Kind::GranuleTxszNotSupported { granule, txsz } => f.write_fmt(format_args!(
                "granule/txsz combination {:?}/{} not supported",
                granule, txsz
            )),
            Kind::TopBitsShouldBeOne { top, va } => f.write_fmt(format_args!(
                "bits [64:{}] should be 1, but they are not in {:?}",
                top, va
            )),
            Kind::TopBitsShouldBeZero { top, va } => f.write_fmt(format_args!(
                "bits [64:{}] should be 0, but they are not in {:?}",
                top, va
            )),
            Kind::NotAligned { value, name } => f.write_fmt(format_args!("\"{}\" ({}) is not aligned", name, value)),
            Kind::IpaDoesNotFitIps { ipa, ips_limit } => f.write_fmt(format_args!(
                "ipa {:#x?} / and or ipa + size are too large, does not fit into the TXSZ space which is limited by address {:#x?}",
                ipa, ips_limit
            )),
            Kind::IpaPlusSizeOverflow { ipa, size } => f.write_fmt(format_args!(
                "ipa + size overflow, {:?}, size {:?}", ipa, size
            )),
            Kind::ProgrammingError(v) => f.write_fmt(format_args!("{}", v)),
            Kind::NotAPowerOfTwo { value } => f.write_fmt(format_args!("{} is not a power of 2", value)),
            Kind::HvReturnTUnrecognized { value, function_name } => f.write_fmt(format_args!("can't map return value of \"{}\" = {} to HvReturnT", function_name, value)),
            Kind::HvReturnTNotSuccess { value, function_name } => f.write_fmt(format_args!("\"{}\" returned {:?}", function_name, value))
        }
    }
}

impl std::error::Error for Kind {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Kind::Mmap(e) => Some(e),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct Error {
    kinds: SmallVec<Kind, 6>,
}

impl Error {
    pub fn from_kind(kind: Kind) -> Self {
        let e = Self {
            kinds: SmallVec::new(),
        };
        e.kinds.push_wrapping(kind);
        e
    }
    fn iter_causes(&self) -> impl Iterator<Item = &Kind> {
        self.kinds.iter().rev()
    }
    fn kind(&self) -> &Kind {
        self.iter_causes().next().unwrap()
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}", self.kind()))
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.kind().source()
    }
}

impl From<Kind> for Error {
    fn from(k: Kind) -> Self {
        Self::from_kind(k)
    }
}
