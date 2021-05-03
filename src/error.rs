pub type Result<T> = core::result::Result<T, Error>;

use std::{alloc::LayoutError, borrow::Cow, str::Utf8Error};

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
    kind: Kind,
    previous: Option<Box<Error>>,
}

impl Error {
    pub fn string<S: Into<Cow<'static, str>>>(s: S) -> Self {
        Self::from_kind(Kind::String(s.into()))
    }
    pub fn from_kind(kind: Kind) -> Self {
        Self {
            kind,
            previous: None,
        }
    }
    pub fn push_kind(self, kind: Kind) -> Self {
        Self {
            kind,
            previous: Some(Box::new(self)),
        }
    }
    fn kind(&self) -> &Kind {
        &self.kind
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}", self.kind))?;

        let mut next = self.previous.as_ref();
        while let Some(next_v) = next.map(|v| v.as_ref()) {
            f.write_fmt(format_args!("\n    Caused by: {}", next_v.kind()))?;
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
