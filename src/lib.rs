use anyhow::{anyhow, bail, Context};
use bindgen::{hv_exit_reason_t, NSObject};
use bitflags::bitflags;
use std::sync::Arc;
use std::{
    convert::{TryFrom, TryInto},
    path::Path,
    thread::JoinHandle,
};
use vm_memory::{
    Address, Bytes, GuestAddress, GuestMemory, GuestMemoryMmap, GuestMemoryRegion, GuestRegionMmap,
    MemoryRegionAddress, MmapRegion,
};

use log::{debug, error, info};

mod page_table;

pub fn get_page_size() -> u64 {
    unsafe { libc::sysconf(libc::_SC_PAGE_SIZE) as u64 }
}

pub(crate) fn is_aligned_to_page_size(value: u64) -> bool {
    align_down_to_page_size(value) == value
}

pub(crate) fn align_down_to_page_size(value: u64) -> u64 {
    value & !(get_page_size() - 1)
}

pub fn align_up_to_page_size(value: u64) -> u64 {
    let aligned_down = align_down_to_page_size(value);
    if aligned_down != value {
        aligned_down + get_page_size()
    } else {
        value
    }
}

#[allow(
    dead_code,
    unused_imports,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    improper_ctypes,
    clippy::all
)]
pub mod bindgen;

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
            ret => return Err(ret),
        };
        Ok(ret)
    }
}

pub struct HfVm {
    memory: Arc<GuestMemoryMmap>,
    entrypoint: Option<GuestAddress>,
    vbar_el1: Option<GuestAddress>,
}

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: GuestAddress,
}

// Memory structure:
// VA_START - the virtual memory of the kernel so that it's in TTBR1.
// At that address we load the kernel itself, including exception vector table.
// VA_START + 1GB = DRAM

pub const VA_PAGE: u64 = 2 << 14;

pub const DRAM_IPA_START: u64 = 0x80_0000;
pub const VA_START: GuestAddress = GuestAddress(0xffff_fff0_0000_0000);
pub const VA_START_OFFSET_DRAM: u64 = DRAM_IPA_START;
pub const DRAM_VA_START: GuestAddress = GuestAddress(VA_START.0 + VA_START_OFFSET_DRAM);

pub const KERNEL_BINARY_MEMORY_MAX_SIZE: u64 = 128 * 1024 * 1024; // 128 Mib

pub const DRAM_KERNEL_BINARY_OFFSET: u64 = 0;

pub const DRAM_TTBR_OFFSET: u64 =
    DRAM_KERNEL_BINARY_OFFSET + KERNEL_BINARY_MEMORY_MAX_SIZE + VA_PAGE;
pub const TTBR_SIZE: usize = core::mem::size_of::<page_table::TranslationTableLevel2_16k>() * 2;

pub const DRAM_KERNEL_USABLE_DRAM_OFFSET: u64 = DRAM_TTBR_OFFSET + TTBR_SIZE as u64 + VA_PAGE;

// this could be configurable, it's just that we don't care yet.
// This is 4 GB.
pub const MEMORY_SIZE: usize = 4 * 1024 * 1024 * 1024;

pub const STACK_SIZE: u64 = 1024 * 1024;
pub const STACK_END: GuestAddress =
    GuestAddress(VA_START.0 + VA_START_OFFSET_DRAM + MEMORY_SIZE as u64);

pub const TXSZ: u64 = 28; // 28 bits are resolved through translation. All the others should be 0 for TTBR0 and 1 for TTBR1.

fn assert_hv_return_t_ok(v: bindgen::hv_return_t, name: &str) -> anyhow::Result<()> {
    let ret = HVReturnT::try_from(v).map_err(|e| {
        anyhow!(
            "unexpected hv_return_t value {:#x} from {}",
            e as usize,
            name
        )
    })?;
    match ret {
        HVReturnT::HV_SUCCESS => Ok(()),
        err => bail!("{}() returned {:?}", name, err),
    }
}

impl HfVm {
    pub fn new() -> anyhow::Result<Self> {
        assert_hv_return_t_ok(unsafe { bindgen::hv_vm_create(null_obj()) }, "hv_vm_create")?;
        debug!(
            "allocating guest memory, VA start: {:x?}, size: {}",
            DRAM_VA_START.0, MEMORY_SIZE
        );
        let mut vm = Self {
            memory: Arc::new(
                GuestMemoryMmap::from_ranges(&[(DRAM_VA_START, MEMORY_SIZE)])
                    .context("error allocating guest memory")?,
            ),
            entrypoint: None,
            vbar_el1: None,
        };
        vm.hf_map_memory(
            vm.memory
                .get_host_address(DRAM_VA_START)
                .context("error getting host address for guest memory start")?,
            DRAM_IPA_START,
            MEMORY_SIZE,
            HvMemoryFlags::ALL,
        )
        .context("error mapping DRAM memory into the guest VM")?;

        let usable_memory_size = (MEMORY_SIZE as u64 - DRAM_KERNEL_USABLE_DRAM_OFFSET) as usize;

        // Configure page tables for *Usable* DRAM.
        // This is the RAM that the kernel is free to use for whatever purpose, e.g. allocating.
        vm.configure_page_tables(
            DRAM_IPA_START + DRAM_KERNEL_USABLE_DRAM_OFFSET,
            DRAM_VA_START
                .checked_add(DRAM_KERNEL_USABLE_DRAM_OFFSET)
                .unwrap(),
            usable_memory_size,
            HvMemoryFlags::ALL,
        )
        .context("error configuring page tables for DRAM")?;
        Ok(vm)
    }

    pub fn get_memory(&self) -> Arc<GuestMemoryMmap> {
        self.memory.clone()
    }

    fn get_ttbr_0_dram_offset(&self) -> u64 {
        DRAM_TTBR_OFFSET
    }

    fn get_ttbr_1_dram_offset(&self) -> u64 {
        self.get_ttbr_0_dram_offset() + TTBR_SIZE as u64
    }

    fn configure_page_tables(
        &mut self,
        ipa: u64,
        va: GuestAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let top_bit_set = (va.0 >> 55) == 1;

        let table_start_dram_offset = if top_bit_set {
            self.get_ttbr_1_dram_offset()
        } else {
            self.get_ttbr_0_dram_offset()
        };

        let page_table_guest_addr = DRAM_VA_START.checked_add(table_start_dram_offset).unwrap();
        let page_table_ptr = self
            .memory
            .get_slice(page_table_guest_addr, TTBR_SIZE)
            .with_context(|| {
                format!(
                    "error getting slice of memory at {:#x?}",
                    page_table_guest_addr.0
                )
            })?
            .as_ptr() as *mut page_table::TranslationTableLevel2_16k;

        let table = unsafe { &mut *page_table_ptr as &mut page_table::TranslationTableLevel2_16k };
        table
            .setup(
                DRAM_IPA_START + table_start_dram_offset,
                va,
                ipa,
                size,
                flags,
            )
            .context("error configuring the Level 2 translation table")?;
        Ok(())
    }

    fn hf_map_memory(
        // void *addr, hv_ipa_t ipa, size_t size, hv_memory_flags_t flags
        &self,
        addr: *mut u8,
        ipa: u64,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        if !is_aligned_to_page_size(addr as u64) {
            bail!("addr {:#x} is not aligned to page size", addr as u64)
        }
        if !is_aligned_to_page_size(ipa) {
            bail!("ipa {:#x} is not aligned to page size", ipa)
        }
        if !is_aligned_to_page_size(size as u64) {
            bail!("size {:#x} is not a multiple of page size", size)
        }

        debug!(
            "calling hv_vm_map: addr={:?}, ipa={:#x}, size={:?}, flags={:?}",
            addr, ipa, size, flags
        );

        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vm_map(addr as *mut _, ipa, size as u64, flags.bits() as u64) },
            "hv_vm_map",
        )
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P) -> anyhow::Result<LoadedElf> {
        let file = std::fs::File::open(filename)?;
        let map = unsafe { memmap::MmapOptions::default().map(&file) }
            .context("error mmmapping ELF file")?;
        let obj = object::File::parse(&map)?;
        use object::read::ObjectSection;
        use object::Object;

        let result = LoadedElf {
            entrypoint: GuestAddress(obj.entry()),
        };

        for section in obj.sections() {
            use object::SectionKind::*;
            let section_name = section.name().with_context(|| {
                format!(
                    "error determining section name at {:#x?}",
                    section.address()
                )
            })?;

            // Assume the exception table is the first piece.
            if let Text = section.kind() {
                self.vbar_el1 = Some(GuestAddress(section.address()))
            }

            match section.kind() {
                Text | Data | ReadOnlyData | UninitializedData => {
                    let flags = match section.kind() {
                        Text => HvMemoryFlags::HV_MEMORY_READ | HvMemoryFlags::HV_MEMORY_EXEC,
                        Data => HvMemoryFlags::HV_MEMORY_READ | HvMemoryFlags::HV_MEMORY_WRITE,
                        ReadOnlyData => HvMemoryFlags::HV_MEMORY_READ,
                        UninitializedData => {
                            HvMemoryFlags::HV_MEMORY_READ | HvMemoryFlags::HV_MEMORY_WRITE
                        }
                        _ => unreachable!(),
                    };
                    let start = align_down_to_page_size(section.address());
                    let end = align_up_to_page_size(section.address() + section.size());
                    let size = (end - start) as usize;
                    debug!(
                        "configuring page tables for section {}, section size {}",
                        section_name,
                        section.size()
                    );

                    // TODO: this assumes the ELF is compiled accordingly and is safe to load
                    // at the specified addresses.
                    let ipa = section.address() - VA_START.0;
                    self.configure_page_tables(ipa, GuestAddress(section.address()), size, flags)?;

                    let data = section.data().with_context(|| {
                        format!("error getting section data for section {}", section_name)
                    })?;
                    if !data.is_empty() {
                        let slice = self
                            .memory
                            .get_slice(GuestAddress(section.address()), section.size() as usize)
                            .with_context(|| {
                                format!(
                                    "error getting the slice of memory for section {}",
                                    section_name
                                )
                            })?;
                        slice.copy_from(data);
                    }
                }
                _ => {}
            }
        }

        self.entrypoint = Some(result.entrypoint);
        Ok(result)
    }

    pub fn vcpu_create_and_run(
        &self,
        entrypoint: Option<GuestAddress>,
    ) -> anyhow::Result<JoinHandle<anyhow::Result<()>>> {
        let memory = self.memory.clone();
        let entrypoint = entrypoint
            .or(self.entrypoint)
            .ok_or_else(|| anyhow!("entrypoint not set"))?;

        let vbar_el1 = self.vbar_el1;
        let ttbr0 = GuestAddress(DRAM_VA_START.0 + self.get_ttbr_0_dram_offset());
        let ttbr1 = GuestAddress(DRAM_VA_START.0 + self.get_ttbr_1_dram_offset());
        Ok(std::thread::spawn(move || {
            let vcpu = VCpu::new(memory).unwrap();
            let start_state = VcpuStartState {
                guest_pc: entrypoint,
                guest_vbar_el1: vbar_el1,
                ttbr0,
                ttbr1,
            };
            vcpu.simple_run_loop(start_state)
        }))
    }
}

#[derive(Debug)]
pub struct VCpu {
    id: u64,
    memory: Arc<GuestMemoryMmap>,
    exit_t: *mut bindgen::hv_vcpu_exit_t,
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

#[derive(Copy, Clone, Debug)]
struct VcpuStartState {
    guest_pc: GuestAddress,
    guest_vbar_el1: Option<GuestAddress>,
    ttbr0: GuestAddress,
    ttbr1: GuestAddress,
}

struct DataAbortFlags(pub u32);

impl DataAbortFlags {
    fn is_valid(&self) -> bool {
        ((self.0 >> 24) & 1) == 1
    }
    fn sas(&self) -> Option<u8> {
        if self.is_valid() {
            Some(((self.0 >> 22) & 0b11) as u8)
        } else {
            None
        }
    }
    fn sas_len(&self) -> Option<u8> {
        self.sas().map(|sas| 1 << sas)
    }
    fn sse(&self) -> Option<bool> {
        if self.is_valid() {
            Some(((self.0 >> 21) & 1) == 1)
        } else {
            None
        }
    }
    fn srt(&self) -> Option<u8> {
        if self.is_valid() {
            Some(((self.0 >> 16) & 31) as u8)
        } else {
            None
        }
    }
    fn sf(&self) -> Option<bool> {
        if self.is_valid() {
            Some(((self.0 >> 15) & 1) == 1)
        } else {
            None
        }
    }
    fn af(&self) -> Option<bool> {
        if self.is_valid() {
            Some(((self.0 >> 15) & 1) == 1)
        } else {
            None
        }
    }

    fn is_write(&self) -> bool {
        ((self.0 >> 6) & 1) == 1
    }

    fn far_is_valid(&self) -> bool {
        ((self.0 >> 10) & 1) == 0
    }

    fn dfsc(&self) -> u8 {
        (self.0 & 0b11111) as u8
    }
}

impl core::fmt::Debug for DataAbortFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("DataAbortFlags[is_valid={}", self.is_valid()))?;
        if let (Some(sas), Some(length), Some(sse), Some(srt), Some(sf), Some(af)) = (
            self.sas(),
            self.sas_len(),
            self.sse(),
            self.srt(),
            self.sf(),
            self.af(),
        ) {
            f.write_fmt(format_args!(
                ", sas={} (length={}), sse={}, srt={} (register=X{}), sf={}, af={}",
                sas, length, sse, srt, srt, sf, af,
            ))?;
        };
        if self.dfsc() == 0b010000 {
            f.write_fmt(format_args!(", far_is_valid={}", self.far_is_valid()))?
        };

        f.write_fmt(format_args!(
            ", is_write={}, dfsc={:#b}]",
            self.is_write(),
            self.dfsc()
        ))?;

        Ok(())
    }
}

#[repr(C)]
struct StartParams {
    dram_start: u64,
    dram_usable_start: u64,
    dram_size: u64,
}

impl VCpu {
    fn new(memory: Arc<GuestMemoryMmap>) -> anyhow::Result<Self> {
        let mut vcpu = Self {
            id: 0,
            memory,
            exit_t: core::ptr::null_mut(),
        };
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_create(&mut vcpu.id, &mut vcpu.exit_t, null_obj()) },
            "hv_vcpu_create",
        )?;
        Ok(vcpu)
    }
    fn exit_t(&self) -> HfVcpuExit {
        unsafe { self.exit_t.as_ref().unwrap().into() }
    }
    fn set_reg(&mut self, reg: bindgen::hv_reg_t, value: u64, name: &str) -> anyhow::Result<()> {
        debug!("setting register {} to {:#x}", name, value);
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_set_reg(self.id, reg, value) },
            "hv_vcpu_set_reg",
        )
    }
    fn set_sys_reg(
        &mut self,
        reg: bindgen::hv_sys_reg_t,
        value: u64,
        name: &str,
    ) -> anyhow::Result<()> {
        debug!("setting system register {} to {:#x}", name, value);
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_set_sys_reg(self.id, reg, value) },
            "hv_vcpu_set_sys_reg",
        )
    }
    fn get_reg(&mut self, reg: bindgen::hv_reg_t) -> anyhow::Result<u64> {
        let mut value = 0u64;
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_get_reg(self.id, reg, &mut value) },
            "hv_vcpu_get_reg",
        )?;
        Ok(value)
    }

    fn get_sys_reg(&mut self, reg: bindgen::hv_sys_reg_t) -> anyhow::Result<u64> {
        let mut value = 0u64;
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_get_sys_reg(self.id, reg, &mut value) },
            "hv_vcpu_get_sys_reg",
        )?;
        Ok(value)
    }

    fn dump_all_registers(&mut self) -> anyhow::Result<()> {
        macro_rules! dump_reg {
            ($reg:ident) => {
                debug!(
                    "{}: {:#x}",
                    &stringify!($reg)[16..],
                    self.get_reg(bindgen::$reg)?
                );
            };
        }

        macro_rules! dump_sys_reg {
            ($reg:ident) => {
                debug!(
                    "{}: {:#x}",
                    &stringify!($reg)[24..],
                    self.get_sys_reg(bindgen::$reg)?
                );
            };
        }

        dump_reg!(hv_reg_t_HV_REG_X0);
        dump_reg!(hv_reg_t_HV_REG_X1);
        dump_reg!(hv_reg_t_HV_REG_X2);
        dump_reg!(hv_reg_t_HV_REG_X3);
        dump_reg!(hv_reg_t_HV_REG_X4);
        dump_reg!(hv_reg_t_HV_REG_X5);
        dump_reg!(hv_reg_t_HV_REG_X6);
        dump_reg!(hv_reg_t_HV_REG_X7);
        dump_reg!(hv_reg_t_HV_REG_X8);
        dump_reg!(hv_reg_t_HV_REG_X9);
        dump_reg!(hv_reg_t_HV_REG_X10);
        dump_reg!(hv_reg_t_HV_REG_X11);
        dump_reg!(hv_reg_t_HV_REG_X12);
        dump_reg!(hv_reg_t_HV_REG_X13);
        dump_reg!(hv_reg_t_HV_REG_X14);
        dump_reg!(hv_reg_t_HV_REG_X15);
        dump_reg!(hv_reg_t_HV_REG_X16);
        dump_reg!(hv_reg_t_HV_REG_X17);
        dump_reg!(hv_reg_t_HV_REG_X18);
        dump_reg!(hv_reg_t_HV_REG_X19);
        dump_reg!(hv_reg_t_HV_REG_X20);
        dump_reg!(hv_reg_t_HV_REG_X21);
        dump_reg!(hv_reg_t_HV_REG_X22);
        dump_reg!(hv_reg_t_HV_REG_X23);
        dump_reg!(hv_reg_t_HV_REG_X24);
        dump_reg!(hv_reg_t_HV_REG_X25);
        dump_reg!(hv_reg_t_HV_REG_X26);
        dump_reg!(hv_reg_t_HV_REG_X27);
        dump_reg!(hv_reg_t_HV_REG_X28);
        dump_reg!(hv_reg_t_HV_REG_X29);
        dump_reg!(hv_reg_t_HV_REG_FP);
        dump_reg!(hv_reg_t_HV_REG_X30);
        dump_reg!(hv_reg_t_HV_REG_LR);
        dump_reg!(hv_reg_t_HV_REG_PC);
        dump_reg!(hv_reg_t_HV_REG_FPCR);
        dump_reg!(hv_reg_t_HV_REG_FPSR);
        dump_reg!(hv_reg_t_HV_REG_CPSR);

        // Stack pointer.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_SP_EL1);

        // Exception table address.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_VBAR_EL1);

        // The PC to return to from exception.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ELR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_FAR_EL1);

        // Page table registers.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_TTBR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_TTBR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_TCR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_SCTLR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_MAIR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR2_EL1);

        // FP state
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_CPACR_EL1);

        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ESR_EL1);

        debug!(
            "ESR EL1 decoded: {:#x?}",
            Syndrome::from(self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ESR_EL1)?)
        );

        Ok(())
    }

    fn print_stack(&mut self) -> anyhow::Result<()> {
        let sp = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SP_EL1)?;
        let len = self.get_stack_end().0 - sp;
        if len == 0 {
            debug!("STACK AT {:#x} is empty", sp);
            return Ok(());
        }
        let mut data = vec![0u8; len as usize];
        debug!("STACK AT {:#x}, length {}", sp, len);
        self.memory.read_slice(&mut data, GuestAddress(sp))?;
        hexdump::hexdump(&data);
        Ok(())
    }

    fn get_stack_end(&self) -> GuestAddress {
        GuestAddress(STACK_END.0 - STACK_SIZE * self.id)
    }

    fn debug_data_abort(&mut self, iss: u32) -> anyhow::Result<()> {
        let dai = DataAbortFlags(iss);
        let write_value = match (dai.is_write(), dai.srt()) {
            (true, Some(srt)) => Some(self.get_reg(bindgen::hv_reg_t_HV_REG_X0 + (srt as u32))?),
            _ => None,
        };
        error!(
            "unhandled data abort: address={:#x?}, flags={:?}, write_value={:#x?}",
            self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_FAR_EL1)?,
            &dai,
            write_value
        );
        Ok(())
    }

    fn simple_run_loop(mut self, start_state: VcpuStartState) -> anyhow::Result<()> {
        debug!("starting a CPU with start state: {:#x?}", &start_state);
        self.set_sys_reg(
            bindgen::hv_sys_reg_t_HV_SYS_REG_SP_EL1,
            self.get_stack_end().0,
            "SP_EL1",
        )
        .context("failed setting stack pointer")?;
        self.set_reg(bindgen::hv_reg_t_HV_REG_PC, start_state.guest_pc.0, "PC")
            .context("failed setting initial program counter")?;

        {
            // Enable floating point
            const FPEN_NO_TRAP: u64 = 0b11 << 20; // disable trapping of FP instructions
            const CPACR_EL1: u64 = FPEN_NO_TRAP;
            self.set_sys_reg(
                bindgen::hv_sys_reg_t_HV_SYS_REG_CPACR_EL1,
                CPACR_EL1,
                "CPACR_EL1",
            )?
        }

        // Copy paste, no clue yet what it does
        const PSR_MODE_EL1H: u64 = 0x0000_0005; //
                                                // const PSR_F_BIT: u64 = 0x0000_0040; // bit 6
                                                // const PSR_I_BIT: u64 = 0x0000_0080; // bit 7
                                                // const PSR_A_BIT: u64 = 0x0000_0100; // bit 8
                                                // const PSR_D_BIT: u64 = 0x0000_0200; // bit 9
        const PSTATE_FAULT_BITS_64: u64 =
            // PSR_MODE_EL1H | PSR_A_BIT | PSR_F_BIT | PSR_I_BIT | PSR_D_BIT;
            PSR_MODE_EL1H;
        self.set_reg(bindgen::hv_reg_t_HV_REG_CPSR, PSTATE_FAULT_BITS_64, "CPSR")?;

        {
            // Set all the required registers.
            {
                let mut tcr_el1 = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_TCR_EL1)?;
                const TG0_GRANULE_16K: u64 = 0b10 << 14;
                const IPS_64GB: u64 = 0b001 << 32; // 64 GB
                const T0SZ: u64 = 28; // so that 36 bits remains.
                const EPD0: u64 = 1 << 7;
                const NFD0: u64 = 1 << 53;
                const SH0_OUTER_SHAREABLE: u64 = 0b10 << 12;
                const ORGN0: u64 = 0b11 << 10;
                const IRGN0: u64 = 0b10 << 8;
                const HA: u64 = 1 << 39;
                tcr_el1 |= TG0_GRANULE_16K | IPS_64GB | T0SZ | HA;
                // | NFD0
                // | SH0_OUTER_SHAREABLE
                // | ORGN0
                // | IRGN0;
                self.set_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_TCR_EL1, tcr_el1, "TCR_EL1")?;
            }
            {
                // We need only 1 type of memory - Normal (not device).
                // 0booooiiii, (oooo != 0000 and iiii != 0000),
                // oooo = 0b111 = Normal memory, Outer Write-Back Transient, Read allocate policy - Allocate, Write Allocate policy - allocate
                // iiii = 0b111 = Normal memory, Inner Write-Back Transient, Read allocate policy - Allocate, Write Allocate policy - allocate
                // I HAVE NO CLUE what this means, but it works with atomics this way :)
                const MAIR_EL1: u64 = 0b0111_0111;
                self.set_sys_reg(
                    bindgen::hv_sys_reg_t_HV_SYS_REG_MAIR_EL1,
                    MAIR_EL1,
                    "MAIR_EL1",
                )?;
            }
            {
                let mut sctlr_el1 = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SCTLR_EL1)?;
                const STAGE_1_ENABLED: u64 = 1;
                sctlr_el1 |= STAGE_1_ENABLED;
                self.set_sys_reg(
                    bindgen::hv_sys_reg_t_HV_SYS_REG_SCTLR_EL1,
                    sctlr_el1,
                    "SCTLR_EL1",
                )?;
            }
            {
                self.set_sys_reg(
                    bindgen::hv_sys_reg_t_HV_SYS_REG_TTBR0_EL1,
                    start_state.ttbr0.0,
                    "TTBR0_EL1",
                )?;
                self.set_sys_reg(
                    bindgen::hv_sys_reg_t_HV_SYS_REG_TTBR1_EL1,
                    start_state.ttbr1.0,
                    "TTBR1_EL1",
                )?;
            }

            // assert_hv_return_t_ok(
            //     unsafe {
            //         bindgen::hv_vcpu_set_pending_interrupt(
            //             self.id,
            //             bindgen::hv_interrupt_type_t_HV_INTERRUPT_TYPE_IRQ,
            //             true,
            //         )
            //     },
            //     "hv_vcpu_set_pending_interrupt",
            // )?;
        };

        {
            let dram_start = DRAM_VA_START;
            let start_params_offset = DRAM_VA_START.0 + DRAM_KERNEL_USABLE_DRAM_OFFSET;
            let start_params = StartParams {
                dram_start: dram_start.0,
                dram_usable_start: start_params_offset
                    + (core::mem::size_of::<StartParams>() as u64),
                dram_size: MEMORY_SIZE as u64,
            };
            let start_params_mem = self
                .memory
                .get_slice(dram_start, core::mem::size_of::<StartParams>())?;
            unsafe {
                core::ptr::copy(
                    &start_params,
                    start_params_mem.as_ptr() as *mut StartParams,
                    1,
                )
            };
            self.set_reg(bindgen::hv_reg_t_HV_REG_X0, dram_start.0, "X0")?;
        }

        // self.enable_soft_debug()?;
        self.spawn_cancel_thread();

        if let Some(vbar_el1) = start_state.guest_vbar_el1 {
            self.set_sys_reg(
                bindgen::hv_sys_reg_t_HV_SYS_REG_VBAR_EL1,
                vbar_el1.0,
                // 0xffff_ffff_0000_0000,
                "VBAR_EL1",
            )?;
        }

        loop {
            assert_hv_return_t_ok(unsafe { bindgen::hv_vcpu_run(self.id) }, "hv_vcpu_run")?;

            let exit_t = self.exit_t();
            if exit_t.reason != HvExitReason::HV_EXIT_REASON_EXCEPTION {
                self.dump_all_registers()?;
                panic!("unexpected exit reason {:?}", exit_t.reason);
            }

            assert_eq!(exit_t.reason, HvExitReason::HV_EXIT_REASON_EXCEPTION);
            match exit_t.decoded_syndrome.exception_class {
                // HVC
                0b010110 => {
                    let iss = exit_t.decoded_syndrome.iss as u16;
                    const NOOP: u8 = 0;
                    const HALT: u8 = 1;
                    const PANIC: u8 = 4;
                    const EXCEPTION: u8 = 5;
                    const SYNCHRONOUS_EXCEPTION: u8 = 6;
                    const PRINT_STRING: u8 = 7;
                    const IRQ: u8 = 8;
                    match iss as u8 {
                        NOOP => {
                            debug!("NOOP HVC received");
                        }
                        HALT => {
                            info!("halt received");
                            return Ok(());
                        }
                        PANIC => {
                            panic!("panic in the guest")
                        }
                        EXCEPTION | SYNCHRONOUS_EXCEPTION | IRQ => {
                            let mut name = match iss as u8 {
                                EXCEPTION => "unknown",
                                SYNCHRONOUS_EXCEPTION => "synchronous",
                                IRQ => "IRQ",
                                _ => unreachable!(),
                            };
                            let el1_syndrome = Syndrome::from(
                                self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ESR_EL1)?,
                            );

                            match el1_syndrome.exception_class {
                                0b100100 | 0b100101 => {
                                    self.debug_data_abort(el1_syndrome.iss)?;
                                    name = "data abort";
                                }
                                _ => {
                                    error!(
                                        "exception class unknown. Full syndrome: {:#x?}",
                                        el1_syndrome
                                    );
                                }
                            }
                            self.dump_all_registers()?;
                            self.print_stack()?;
                            panic!("EL1 -> EL1 exception: {}", name);
                        }
                        PRINT_STRING => {
                            let addr = self.get_reg(bindgen::hv_reg_t_HV_REG_X0)?;
                            let len = self.get_reg(bindgen::hv_reg_t_HV_REG_X1)?;
                            let slice = self.memory.get_slice(GuestAddress(addr), len as usize)?;
                            let slice = unsafe {
                                core::slice::from_raw_parts(slice.as_ptr(), len as usize)
                            };
                            print!("{}", core::str::from_utf8(slice)?);
                        }
                        other => {
                            panic!("unsupported HVC value {:x}", other);
                        }
                    }
                }
                // some memory failure
                0b100000 => {
                    error!("memory failure");
                    self.dump_all_registers()?;
                    self.print_stack()?;
                    error!("{:#x?}", self.exit_t());
                    panic!("memory failure");
                }
                0b100100 => {
                    self.debug_data_abort(self.exit_t().decoded_syndrome.iss)?;
                    panic!("data abort EL1 -> EL2");
                }
                other => {
                    error!("unsupported exception class {:b}", other)
                }
            }

            // Testing interrupts
            // assert_hv_return_t_ok(
            //     unsafe {
            //         bindgen::hv_vcpu_set_pending_interrupt(
            //             self.id,
            //             bindgen::hv_interrupt_type_t_HV_INTERRUPT_TYPE_IRQ,
            //             true,
            //         )
            //     },
            //     "hv_vcpu_set_pending_interrupt",
            // )?;
        }
    }

    fn spawn_cancel_thread(&mut self) {
        let mut id = self.id;
        std::thread::spawn(move || {
            use std::time::Duration;
            std::thread::sleep(Duration::from_secs(1));
            assert_hv_return_t_ok(
                unsafe { bindgen::hv_vcpus_exit(&mut id, 1) },
                "hv_vcpus_exit",
            )
        });
    }

    fn enable_soft_debug(mut self) -> anyhow::Result<()> {
        // Soft debug
        const KDE: u64 = 1 << 13;
        const SOFTWARE_STEP_ENABLE: u64 = 1;
        let mdscr_el1 = KDE | SOFTWARE_STEP_ENABLE;
        self.set_sys_reg(
            bindgen::hv_sys_reg_t_HV_SYS_REG_MDSCR_EL1,
            mdscr_el1,
            "MDSCR_EL1",
        )?;
        Ok(())
    }
}

pub struct Syndrome {
    exception_class: u8,
    iss: u32,
    iss2: u8,
    il_32_bit: bool,
    original_value: u64,
}

const EXC_HVC: u8 = 0b010110;
const EXC_MMU_LOWER: u8 = 0b100000;
const EXC_MMU_SAME: u8 = 0b100001;
const EXC_DATA_ABORT_LOWER: u8 = 0b100100;
const EXC_DATA_ABORT_SAME: u8 = 0b100101;

struct InstructionAbortFlags(u32);
impl core::fmt::Debug for InstructionAbortFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ds = f.debug_struct("InstructionAbortFlags");

        let ifsc = self.0 & 0b111111;
        ds.field("ifsc (status code)", &ifsc);
        let ifsc_desc = match ifsc {
            0b000100 => "Translation fault, level 0",
            0b000101 => "Translation fault, level 1",
            0b000110 => "Translation fault, level 2",
            0b000111 => "Translation fault, level 3",
            0b001011 => "Access flag fault, level 3",
            _ => "[OTHER, look at the docs]",
        };
        ds.field("IFSC description", &ifsc_desc);
        if ifsc == 0b100000 {
            let fnv = ((self.0 >> 10) & 1) == 1;
            ds.field("fnv", &fnv);

            let set = (self.0 >> 11) & 0b11;
            let set = match set {
                0b00 => "recoverable state",
                0b10 => "uncontainable",
                0b11 => "restartable state",
                _ => "[RESERVED]",
            };
            ds.field("set", &set);
        };
        ds.finish()
    }
}

impl Syndrome {
    fn exc_class_name(&self) -> &'static str {
        match self.exception_class {
            // some memory failure
            EXC_HVC => "HVC",
            EXC_MMU_LOWER => "Instruction abort (MMU) from lower EL",
            EXC_MMU_SAME => "Instruction abort (MMU) fault from same EL",
            EXC_DATA_ABORT_LOWER => "Data abort from a lower exception level",
            EXC_DATA_ABORT_SAME => "Data abort from the same exception level",
            _ => "unknown",
        }
    }
    fn data_abort_flags(&self) -> Option<DataAbortFlags> {
        match self.exception_class {
            EXC_DATA_ABORT_LOWER | EXC_DATA_ABORT_SAME => Some(DataAbortFlags(self.iss)),
            _ => None,
        }
    }
    fn instruction_abort_flags(&self) -> Option<InstructionAbortFlags> {
        match self.exception_class {
            EXC_MMU_SAME | EXC_MMU_LOWER => Some(InstructionAbortFlags(self.iss)),
            _ => None,
        }
    }
}

impl core::fmt::Debug for Syndrome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ds = f.debug_struct("Syndrome");
        ds.field("exception_class", &self.exception_class)
            .field("iss", &self.iss)
            .field("iss2", &self.iss2)
            .field("il32_bit", &self.il_32_bit)
            .field("original_value", &self.original_value)
            .field("exc_class_name()", &self.exc_class_name());
        if let Some(flags) = self.data_abort_flags() {
            ds.field("data_abort_flags()", &flags);
        };
        if let Some(flags) = self.instruction_abort_flags() {
            ds.field("instruction_abort_flags()", &flags);
        };
        ds.finish()
    }
}

impl From<u64> for Syndrome {
    fn from(s: u64) -> Self {
        let eclass = ((s >> 26) & 0b111111) as u8;
        let iss = (s & ((1 << 25) - 1)) as u32;
        let iss2 = ((s >> 32) & 31) as u8;
        let il_32_bit = (s >> 25) & 1 > 0;
        Self {
            exception_class: eclass,
            iss,
            original_value: s,
            il_32_bit,
            iss2,
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_page_size_16k() {
        assert_eq!(get_page_size(), 16384)
    }

    #[test]
    fn test_align_down_to_page_size() {
        assert_eq!(align_down_to_page_size(16385), 16384)
    }

    #[test]
    fn test_is_aligned_down_to_page_size() {
        assert_eq!(is_aligned_to_page_size(0x0000000101408000), true);
        assert_eq!(is_aligned_to_page_size(0x0000000103194000), true);
    }
}
