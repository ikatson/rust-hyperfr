use std::ffi::c_void;

#[repr(C)]
enum HVReturnT {
    HV_SUCCESS,
    HV_ERROR,
    HV_BUSY,
    HV_BAD_ARGUMENT,
    HV_NO_RESOURCES,
    HV_NO_DEVICE,
    HV_UNSUPPORTED,
}

type hv_vm_config_t = * const c_void;

extern "C" {
    fn hv_vm_create() -> HVReturnT;
}