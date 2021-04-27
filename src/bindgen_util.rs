use crate::{
    aarch64_debug::Syndrome,
    bindgen::{self, hv_exit_reason_t, NSObject},
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
