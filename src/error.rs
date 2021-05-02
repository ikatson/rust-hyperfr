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
            Some(unsafe { &*self.items[true_idx].as_ptr() })
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

    impl<T: Sized, const S: usize> Default for SmallVec<T, S> {
        fn default() -> Self {
            Self::new()
        }
    }
}

use std::{alloc::LayoutError, borrow::Cow, str::Utf8Error};

use smallvec::SmallVec;

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress},
    translation_table::Aarch64TranslationGranule,
};

#[derive(Debug)]
pub enum Kind {
    String(Cow<'static, str>),
    Context(Cow<'static, str>),
    UnsupportedInput(Cow<'static, str>),
    ProgrammingError(Cow<'static, str>),
    MmapGuestMemory(std::io::Error),
    ByteOrderWriteError(std::io::Error),
    MmapElfFile(std::io::Error),
    FileOpen(std::io::Error),
    ObjectLibrary(object::Error),
    InvalidGuestIpaAddress(GuestIpaAddress),
    Layout(LayoutError),
    Utf8Error(Utf8Error),
    TranslationForLoadSegment {
        idx: usize,
        segment_address: u64,
        segment_size: u64,
        aligned_size: u64,
        ipa: u64,
        va: u64,
        flags: crate::HvMemoryFlags,
    },
    ErrorReadingSectionName {
        address: u64,
    },
    ErrorReadingSectionData {
        section_address: u64,
    },

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
    ElfLoaderCannotSimulateAddressLookupInSection {
        va: GuestVaAddress,
        section_address: u64,
        segment_idx: usize,
    },
    NoExceptionVectorTable,
    SimulateTranslationError {
        va: GuestVaAddress,
    },
}

impl core::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::MmapGuestMemory(e) => f.write_fmt(format_args!("error mmap'ing guest memory: {}", e)),
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
            Kind::HvReturnTNotSuccess { value, function_name } => f.write_fmt(format_args!("\"{}\" returned {:?}", function_name, value)),
            Kind::MmapElfFile(e) => f.write_fmt(format_args!("error mmap'ing ELF file: {}", e)),
            Kind::FileOpen(e) => f.write_fmt(format_args!("error opening file: {}", e)),
            Kind::ObjectLibrary(e) => f.write_fmt(format_args!("error from \"object\" crate: {}", e)),
            Kind::Layout(l) => f.write_fmt(format_args!("layout error: {}", l)),
            Kind::TranslationForLoadSegment { idx, segment_address, segment_size, aligned_size, ipa, va, flags } => {
                f.write_fmt(
                    format_args!(
                        "configuring translation tables for LOAD segment {}, address {:#x?}, size {}, aligned size {}, IPA {:#x?}, VA {:#x?}, flags: {:?}",
                        idx,
                        segment_address,
                        segment_size,
                        aligned_size,
                        ipa,
                        va,
                        flags,
                    ))
            }
            Kind::ErrorReadingSectionName { address } => f.write_fmt(format_args!("error reading section name at {:#x?}", address)),
            Kind::ErrorReadingSectionData { section_address } => f.write_fmt(format_args!("error reading section data at {:#x?}", section_address)),
            Kind::ElfLoaderCannotSimulateAddressLookupInSection { va, section_address, segment_idx } => {
                f.write_fmt(format_args!(
                    "couldn't lookup address {:?} for section at {:#x?}, it should have been mapped together with segment {}",
                    va,
                    section_address,
                    segment_idx
                ))
            }
            Kind::NoExceptionVectorTable => f.write_str("cound not find symbol \"exception_vector_table\""),
            Kind::Context(v) => f.write_str(&v),
            Kind::UnsupportedInput(v) => f.write_str(&v),
            Kind::ByteOrderWriteError(e) => f.write_fmt(format_args!("error writing to slice: {}", e)),
            Kind::SimulateTranslationError { va } => f.write_fmt(format_args!("cannot find address {:?} in translation tables", va)),
            Kind::String(s) => f.write_str(s),
            Kind::Utf8Error(e) => f.write_fmt(format_args!("{}", e))
        }
    }
}

impl std::error::Error for Kind {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Kind::MmapGuestMemory(e) => Some(e),
            Kind::MmapElfFile(e) => Some(e),
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
        let mut e = Self {
            kinds: SmallVec::new(),
        };
        e.kinds.push_wrapping(kind);
        e
    }
    pub fn push_kind(&mut self, kind: Kind) {
        self.kinds.push_wrapping(kind);
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

impl From<object::Error> for Error {
    fn from(e: object::Error) -> Self {
        Self::from_kind(Kind::ObjectLibrary(e))
    }
}

impl From<LayoutError> for Error {
    fn from(e: LayoutError) -> Self {
        Self::from_kind(Kind::Layout(e))
    }
}

impl From<Utf8Error> for Error {
    fn from(e: Utf8Error) -> Self {
        Self::from_kind(Kind::Utf8Error(e))
    }
}

pub trait ErrorContext<T> {
    fn context<C: Into<Cow<'static, str>>>(self, value: C) -> Result<T>;
    fn with_context<C: Into<Cow<'static, str>>, F: FnOnce() -> C>(self, cb: F) -> Result<T>;
}

impl<T, E> ErrorContext<T> for core::result::Result<T, E>
where
    E: Into<Error>,
{
    fn context<C: Into<Cow<'static, str>>>(self, value: C) -> Result<T> {
        self.map_err(|e| {
            let mut err = e.into();
            err.push_kind(Kind::Context(value.into()));
            err
        })
    }

    fn with_context<C: Into<Cow<'static, str>>, F: FnOnce() -> C>(self, cb: F) -> Result<T> {
        self.map_err(|e| {
            let mut err = e.into();
            err.push_kind(Kind::Context(cb().into()));
            err
        })
    }
}
