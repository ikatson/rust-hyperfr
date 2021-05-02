use crate::{
    aarch64_debug::Syndrome,
    bindgen::{self, hv_exit_reason_t, NSObject},
    error::Kind,
};
use bitflags::bitflags;
use std::convert::{TryFrom, TryInto};

pub const fn null_obj() -> NSObject {
    NSObject(core::ptr::null_mut() as *mut _)
}

#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
#[derive(Debug, PartialEq, Eq)]
pub enum HvExitReason {
    HV_EXIT_REASON_CANCELED,
    HV_EXIT_REASON_EXCEPTION,
    HV_EXIT_REASON_VTIMER_ACTIVATED,
    HV_EXIT_REASON_UNKNOWN,
}

impl TryFrom<bindgen::hv_exit_reason_t> for HvExitReason {
    type Error = hv_exit_reason_t;

    fn try_from(value: bindgen::hv_exit_reason_t) -> Result<Self, Self::Error> {
        use HvExitReason::*;
        let ok = match value {
            bindgen::hv_exit_reason_t_HV_EXIT_REASON_CANCELED => HV_EXIT_REASON_CANCELED,
            bindgen::hv_exit_reason_t_HV_EXIT_REASON_EXCEPTION => HV_EXIT_REASON_EXCEPTION,
            bindgen::hv_exit_reason_t_HV_EXIT_REASON_VTIMER_ACTIVATED => {
                HV_EXIT_REASON_VTIMER_ACTIVATED
            }
            bindgen::hv_exit_reason_t_HV_EXIT_REASON_UNKNOWN => HV_EXIT_REASON_UNKNOWN,
            v => return Err(v),
        };
        Ok(ok)
    }
}

#[derive(Debug)]
pub struct HfVcpuExit {
    pub reason: HvExitReason,
    pub exception: bindgen::hv_vcpu_exit_exception_t,
    pub decoded_syndrome: Syndrome,
}

impl From<&bindgen::hv_vcpu_exit_t> for HfVcpuExit {
    fn from(v: &bindgen::hv_vcpu_exit_t) -> Self {
        Self {
            reason: v.reason.try_into().unwrap(),
            exception: v.exception,
            decoded_syndrome: Syndrome::from(v.exception.syndrome),
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
            ret => return Err(ret),
        };
        Ok(ret)
    }
}

pub fn assert_hv_return_t_ok(v: bindgen::hv_return_t, name: &'static str) -> crate::Result<()> {
    let ret = HVReturnT::try_from(v).map_err(|e| Kind::HvReturnTUnrecognized {
        value: e,
        function_name: name,
    })?;
    match &ret {
        HVReturnT::HV_SUCCESS => Ok(()),
        err => {
            return Err(Kind::HvReturnTNotSuccess {
                value: ret,
                function_name: name,
            }
            .into())
        }
    }
}
