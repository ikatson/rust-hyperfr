pub type Result<T> = core::result::Result<T, Error>;

use std::{alloc::LayoutError, backtrace::Backtrace, borrow::Cow, str::Utf8Error};

use crate::{
    addresses::{GuestIpaAddress, GuestVaAddress},
    translation_table::Aarch64TranslationGranule,
};

#[derive(Debug)]
pub enum Kind {
    String(Cow<'static, str>),
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
            Kind::MmapGuestMemory(e) => write!(f, "error mmap'ing guest memory: {}", e),
            Kind::InvalidGuestIpaAddress(addr) => {
                f.write_fmt(format_args!("invalid guest address: {:?}", addr))
            }
            Kind::InvalidGuestMemorySlice { ipa, size } => write!(f,
                "invalid guest memory slice (out of bounds): ipa {:?}, size {}",
                ipa, size
            ),
            Kind::GranuleTxszNotSupported { granule, txsz } => write!(f,
                "granule/txsz combination {:?}/{} not supported",
                granule, txsz
            ),
            Kind::TopBitsShouldBeOne { top, va } => write!(f,
                "bits [64:{}] should be 1, but they are not in {:?}",
                top, va
            ),
            Kind::TopBitsShouldBeZero { top, va } => write!(f,
                "bits [64:{}] should be 0, but they are not in {:?}",
                top, va
            ),
            Kind::NotAligned { value, name } => write!(f, "\"{}\" ({}) is not aligned", name, value),
            Kind::IpaDoesNotFitIps { ipa, ips_limit } => write!(f,
                "ipa {:#x?} / and or ipa + size are too large, does not fit into the TXSZ space which is limited by address {:#x?}",
                ipa, ips_limit
            ),
            Kind::IpaPlusSizeOverflow { ipa, size } => write!(f,
                "ipa + size overflow, {:?}, size {:?}", ipa, size
            ),
            Kind::NotAPowerOfTwo { value } => write!(f, "{} is not a power of 2", value),
            Kind::HvReturnTUnrecognized { value, function_name } => write!(f, "can't map return value of \"{}\" = {} to HvReturnT", function_name, value),
            Kind::HvReturnTNotSuccess { value, function_name } => write!(f, "\"{}\" returned {:?}", function_name, value),
            Kind::MmapElfFile(e) => write!(f, "error mmap'ing ELF file: {}", e),
            Kind::FileOpen(e) => write!(f, "error opening file: {}", e),
            Kind::ObjectLibrary(e) => write!(f, "error from \"object\" crate: {}", e),
            Kind::Layout(l) => write!(f, "layout error: {}", l),
            Kind::TranslationForLoadSegment { idx, segment_address } => write!(f,
                "configuring translation tables for LOAD segment {}, address {:#x?}",
                idx,
                segment_address,
            ),
            Kind::ErrorReadingSectionName { address } => write!(f, "error reading section name at {:#x?}", address),
            Kind::ErrorReadingSectionData { section_address } => write!(f, "error reading section data at {:#x?}", section_address),
            Kind::ElfLoaderCannotSimulateAddressLookupInSection { va, section_address, segment_idx } => {
                f.write_fmt(format_args!(
                    "couldn't lookup address {:?} for section at {:#x?}, it should have been mapped together with segment {}",
                    va,
                    section_address,
                    segment_idx
                ))
            }
            Kind::NoExceptionVectorTable => f.write_str("cound not find symbol \"exception_vector_table\""),
            Kind::ByteOrderWriteError(e) => write!(f, "error writing to slice: {}", e),
            Kind::SimulateTranslationError { va } => write!(f, "cannot find address {:?} in translation tables", va),
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
    kind: Kind,
    previous: Option<Box<Error>>,
    backtrace: Option<Backtrace>,
}

impl Error {
    pub fn string<S: Into<Cow<'static, str>>>(s: S) -> Self {
        Self::from_kind(Kind::String(s.into()))
    }
    pub fn from_kind_no_backtrace(kind: Kind) -> Self {
        Self {
            kind,
            previous: None,
            backtrace: None,
        }
    }
    pub fn from_kind(kind: Kind) -> Self {
        Self {
            kind,
            previous: None,
            backtrace: Some(Backtrace::capture()),
        }
    }
    pub fn push_kind(self, kind: Kind) -> Self {
        let mut new_self = Self::from_kind_no_backtrace(kind);
        new_self.previous = Some(Box::new(self));
        new_self
    }
    fn kind(&self) -> &Kind {
        &self.kind
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)?;

        let mut next = self.previous.as_ref();
        while let Some(next_v) = next.map(|v| v.as_ref()) {
            write!(f, "\n    Caused by: {}", next_v.kind())?;
            if let Some(bt) = next_v.backtrace.as_ref() {
                write!(f, "\n\nBacktrace:\n{}", bt)?;
            }
            next = next_v.previous.as_ref();
        }
        Ok(())
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
            let err = e.into();
            err.push_kind(Kind::String(value.into()))
        })
    }

    fn with_context<C: Into<Cow<'static, str>>, F: FnOnce() -> C>(self, cb: F) -> Result<T> {
        self.map_err(|e| {
            let err = e.into();
            err.push_kind(Kind::String(cb().into()))
        })
    }
}
