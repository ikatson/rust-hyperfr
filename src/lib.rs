use std::convert::TryFrom;
use address::{Address, Addresses};
use anyhow::{anyhow, bail};
use bindgen::NSObject;
use bitflags::bitflags;

#[allow(
    dead_code,
    unused_imports,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    improper_ctypes,
    clippy::all,
)]
pub mod bindgen;
pub mod address;

pub const fn null_obj() -> NSObject {
    NSObject(core::ptr::null_mut() as *mut _)
}

#[derive(Debug)]
#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
pub enum HVReturnT {
    HV_SUCCESS,
    HV_ERROR,
    HV_BUSY,
    HV_BAD_ARGUMENT,
    HV_ILLEGAL_GUEST_STATE,
    HV_NO_RESOURCES,
    HV_NO_DEVICE,
    HV_DENIED,
    HV_UNSUPPORTED,
}

impl TryFrom<bindgen::hv_return_t> for HVReturnT {
    type Error = bindgen::hv_return_t;

    fn try_from(value: bindgen::hv_return_t) -> Result<Self, Self::Error> {
        use bindgen as b;
        use HVReturnT::*;
        let ret = match value {
            b::HV_SUCCESS => HV_SUCCESS,
            b::HV_ERROR => HV_ERROR,
            b::HV_BUSY => HV_BUSY,
            b::HV_BAD_ARGUMENT => HV_BAD_ARGUMENT,
            b::HV_ILLEGAL_GUEST_STATE => HV_ILLEGAL_GUEST_STATE,
            b::HV_NO_RESOURCES => HV_NO_RESOURCES,
            b::HV_NO_DEVICE => HV_NO_DEVICE,
            b::HV_DENIED => HV_DENIED,
            b::HV_UNSUPPORTED => HV_UNSUPPORTED,
            ret => return Err(ret)
        };
        Ok(ret)
    }
}

pub struct HfVm {}

impl HfVm {
    pub fn new() -> anyhow::Result<Self> {
        let result = unsafe {
            bindgen::hv_vm_create(null_obj())
        };
        let res = HVReturnT::try_from(result).map_err(|e| anyhow!("unexpected hv_return_t value {:#x} from hv_vm_create", e as usize))?;
        match res {
            HVReturnT::HV_SUCCESS => Ok(Self{}),
            err => bail!("hv_vm_create() returned {:?}", err)
        }
    }

    pub fn map_memory(
        // void *addr, hv_ipa_t ipa, size_t size, hv_memory_flags_t flags
        &mut self,
        addr: Address,
        ipa: Address,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {

        let addrs = Addresses::default();
        if !addrs.is_aligned(addr) {
            bail!("addr is not aligned to page size")
        }
        if !addrs.is_aligned(ipa) {
            bail!("ipa is not aligned to page size")
        }
        if !addrs.is_aligned(Address::new_from_usize(size)) {
            bail!("size is not a multiple of page size")
        }

        // hv_return_t hv_vm_map(void *addr, hv_ipa_t ipa, size_t size, hv_memory_flags_t flags);
        // bindgen::hv_vm_map(addr, ipa, size, flags)
        let result = unsafe {bindgen::hv_vm_map(addr.as_usize() as *mut _, ipa.as_usize() as u64, size as u64, flags.bits() as u64)};
        let ret = HVReturnT::try_from(result).map_err(|e| anyhow!("unexpected hv_return_t value {:#x} from hv_vm_map", e as usize))?;
        match ret {
            HVReturnT::HV_SUCCESS => Ok(()),
            err => bail!("hv_vm_map() returned {:?}", err)
        }
    }
}


bitflags! {
    pub struct HvMemoryFlags: u32 {
        const HV_MEMORY_READ        = bindgen::HV_MEMORY_READ;
        const HV_MEMORY_WRITE        = bindgen::HV_MEMORY_WRITE;
        const HV_MEMORY_EXEC        = bindgen::HV_MEMORY_EXEC;
        const ALL = Self::HV_MEMORY_READ.bits | Self::HV_MEMORY_WRITE.bits | Self::HV_MEMORY_EXEC.bits;
    }
}