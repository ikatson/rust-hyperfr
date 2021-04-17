use address::{Address, Addresses};
use anyhow::{anyhow, bail, Context};
use bindgen::{hv_exit_reason_t, NSObject};
use bitflags::bitflags;
use std::{convert::{TryFrom, TryInto}, ops::Add, path::Path, thread::JoinHandle};
use std::io::Write;

mod page_table;

pub const DRAM_MEM_START: usize = 0x8000_0000; // 2 GB.

pub mod address;
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

pub struct HfVm {}

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: usize,
    maps: Vec<memmap::MmapMut>,
}

impl HfVm {
    pub fn new() -> anyhow::Result<Self> {
        let result = unsafe { bindgen::hv_vm_create(null_obj()) };
        let res = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vm_create",
                e as usize
            )
        })?;
        match res {
            HVReturnT::HV_SUCCESS => Ok(Self {}),
            err => bail!("hv_vm_create() returned {:?}", err),
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
        dbg!(addr, ipa, size, flags);
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
        let result = unsafe {
            bindgen::hv_vm_map(
                addr.as_usize() as *mut _,
                ipa.as_usize() as u64,
                size as u64,
                flags.bits() as u64,
            )
        };
        let ret = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vm_map",
                e as usize
            )
        })?;
        match ret {
            HVReturnT::HV_SUCCESS => Ok(()),
            err => bail!("hv_vm_map() returned {:?}", err),
        }
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P, addresses: Addresses, offset: usize) -> anyhow::Result<LoadedElf> {
        let file = std::fs::File::open(filename)?;
        let map = unsafe {memmap::MmapOptions::default().map(&file)}?;
        let obj = object::File::parse(&map)?;
        use object::Object;
        use object::read::ObjectSection;

        let mut result = LoadedElf{
            entrypoint: obj.entry() as usize + offset,
            ..Default::default()
        };

        let mut min_address = usize::MAX;
        let mut max_address = usize::MIN;

        for section in obj.sections() {
            use object::SectionKind::*;
            match section.kind() {
                Text | Data | ReadOnlyData => {
                    min_address = min_address.min(addresses.align(section.address()).as_usize());
                    max_address = max_address.max(addresses.align_up(section.address() + section.size()).as_usize());
                },
                _ => {}
            }
        }

        println!("Min addr: {:x}, max addr: {:x}", min_address, max_address);

        let mut mmap = memmap::MmapOptions::default().len(max_address - min_address).map_anon()?;
        for section in obj.sections() {
            use object::SectionKind::*;
            match section.kind() {
                Text | Data | ReadOnlyData => {
                    let offset = section.address() as usize - min_address;
                    let data = &mut mmap.as_mut()[offset..offset + section.size() as usize];
                    data.copy_from_slice(section.data().unwrap());
                },
                other => {
                    println!("ignoring section {:?} with kind {:?}", section.name(), other);
                }
            }
        }

        self.map_memory(mmap.as_ptr().into(), (offset + min_address).into(), mmap.len(), HvMemoryFlags::ALL)?;
        result.maps.push(mmap);

        // for section in obj.sections() {
        //     use object::SectionKind::*;
        //     match section.kind() {
        //         Text | Data | ReadOnlyData => {
        //             dbg!(section.name().unwrap_or_default(), section.kind());
        //             let aligned_start = addresses.align(section.address());
        //             let start_offset = section.address() as usize - aligned_start.as_usize();
        //             let aligned_end = addresses.align_up(section.address() + section.size());
        //             let mmap_len = aligned_end.as_usize() - aligned_start.as_usize();
        //             let mut mmap = memmap::MmapOptions::default().len(mmap_len).map_anon()?;
        //             let flags = match section.kind() {
        //                 Text => HvMemoryFlags::HV_MEMORY_EXEC | HvMemoryFlags::HV_MEMORY_READ,
        //                 Data => HvMemoryFlags::HV_MEMORY_WRITE | HvMemoryFlags::HV_MEMORY_READ,
        //                 ReadOnlyData => HvMemoryFlags::HV_MEMORY_READ,
        //                 _ => unreachable!()
        //             };
        //             self.map_memory(Address::from(mmap.as_ptr()), offset.into(), mmap_len, flags)?;

        //             let data = &mut mmap.as_mut()[start_offset..(start_offset + section.size() as usize)];
        //             data.copy_from_slice(section.data().unwrap());

        //             result.maps.push(mmap);
        //         }
        //         Tls => unimplemented!(),
        //         UninitializedTls => unimplemented!(),
        //         TlsVariables => unimplemented!(),
        //         other => {
        //             println!("ignoring section {:?} with kind {:?}", section.name(), other);
        //         },
        //     }
        // }

        // dbg!(obj.entry());
        // dbg!(obj.object_map());
        Ok(result)
    }

    pub fn vcpu_create_and_run<F>(&mut self, entrypoint: Address, callback: F) -> JoinHandle<anyhow::Result<()>>
    where
        F: FnMut(anyhow::Result<HfVcpuExit>) -> anyhow::Result<()> + Send + 'static,
    {
        let join = std::thread::spawn(move || {
            let vcpu = VCpu::new().unwrap();
            let start_state = VcpuStartState {
                guest_pc: entrypoint,
            };
            vcpu.simple_run_loop(start_state, callback)
        });
        join
    }
}

#[derive(Debug)]
pub struct VCpu {
    id: u64,
    exit_t: *mut bindgen::hv_vcpu_exit_t,
}

#[derive(Debug)]
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

struct VcpuStartState {
    guest_pc: Address,
}

impl VCpu {
    fn new() -> anyhow::Result<Self> {
        let mut vcpu = Self {
            id: 0,
            exit_t: core::ptr::null_mut(),
        };
        let result = unsafe { bindgen::hv_vcpu_create(&mut vcpu.id, &mut vcpu.exit_t, null_obj()) };
        let ret = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vcpu_create",
                e as usize
            )
        })?;
        match ret {
            HVReturnT::HV_SUCCESS => Ok(vcpu),
            err => bail!("hv_vcpu_create() returned {:?}", err),
        }
    }
    fn exit_t(&self) -> HfVcpuExit {
        unsafe { self.exit_t.as_ref().unwrap().into() }
    }
    fn set_reg(&mut self, reg: bindgen::hv_reg_t, value: u64) -> anyhow::Result<()> {
        let result = unsafe { bindgen::hv_vcpu_set_reg(self.id, reg, value) };
        let ret = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vcpu_set_reg",
                e as usize
            )
        })?;
        match ret {
            HVReturnT::HV_SUCCESS => {}
            err => bail!("hv_vcpu_set_reg() returned {:?}", err),
        };
        Ok(())
    }
    fn set_sys_reg(&mut self, reg: bindgen::hv_sys_reg_t, value: u64) -> anyhow::Result<()> {
        let result = unsafe { bindgen::hv_vcpu_set_sys_reg(self.id, reg, value) };
        let ret = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vcpu_set_sys_reg",
                e as usize
            )
        })?;
        match ret {
            HVReturnT::HV_SUCCESS => {}
            err => bail!("hv_vcpu_set_sys_reg() returned {:?}", err),
        };
        Ok(())
    }
    fn get_reg(&mut self, reg: bindgen::hv_reg_t) -> anyhow::Result<u64> {
        let mut value = 0u64;
        let result = unsafe { bindgen::hv_vcpu_get_reg(self.id, reg, &mut value) };
        let ret = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vcpu_get_reg",
                e as usize
            )
        })?;
        match ret {
            HVReturnT::HV_SUCCESS => {}
            err => bail!("hv_vcpu_get_reg() returned {:?}", err),
        };
        Ok(value)
    }

    fn get_sys_reg(&mut self, reg: bindgen::hv_sys_reg_t) -> anyhow::Result<u64> {
        let mut value = 0u64;
        let result = unsafe { bindgen::hv_vcpu_get_sys_reg(self.id, reg, &mut value) };
        let ret = HVReturnT::try_from(result).map_err(|e| {
            anyhow!(
                "unexpected hv_return_t value {:#x} from hv_vcpu_get_reg",
                e as usize
            )
        })?;
        match ret {
            HVReturnT::HV_SUCCESS => {}
            err => bail!("hv_vcpu_get_reg() returned {:?}", err),
        };
        Ok(value)
    }

    fn dump_all_registers(&mut self) -> anyhow::Result<()> {
        macro_rules! dump_reg {
            ($reg:ident) => {
                println!("{}: {:#x}", stringify!($reg), self.get_reg(bindgen::$reg)?);
            }
        }

        macro_rules! dump_sys_reg {
            ($reg:ident) => {
                println!("{}: {:#x}", stringify!($reg), self.get_sys_reg(bindgen::$reg)?);
            }
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

        // TOOD: forgot what this one does.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_VBAR_EL1);

        // The PC to return to from exception.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ELR_EL1);

        // Page table registers.
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_TTBR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_TTBR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_TCR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_SCTLR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR2_EL1);

        Ok(())
    }

    fn simple_run_loop<F>(
        mut self,
        start_state: VcpuStartState,
        mut callback: F,
    ) -> anyhow::Result<()>
    where
        F: FnMut(anyhow::Result<HfVcpuExit>) -> anyhow::Result<()>,
    {
        let stack_size = 1024 * 1024u64;
        self.set_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SP_EL1, DRAM_MEM_START as u64 + stack_size)?;
        self.set_reg(
            bindgen::hv_reg_t_HV_REG_PC,
            start_state.guest_pc.as_usize() as u64,
        )
        .context("failed setting initial program counter")?;

        // Copy paste, no clue yet what it does
        const PSR_MODE_EL1H: u64 = 0x0000_0005;
        const PSR_F_BIT: u64 = 0x0000_0040;
        const PSR_I_BIT: u64 = 0x0000_0080;
        const PSR_A_BIT: u64 = 0x0000_0100;
        const PSR_D_BIT: u64 = 0x0000_0200;
        const PSTATE_FAULT_BITS_64: u64 = PSR_MODE_EL1H | PSR_A_BIT | PSR_F_BIT | PSR_I_BIT | PSR_D_BIT;
        self.set_reg(bindgen::hv_reg_t_HV_REG_CPSR, PSTATE_FAULT_BITS_64).unwrap();

        loop {
            self.dump_all_registers().unwrap();
            let result = unsafe { bindgen::hv_vcpu_run(self.id) };
            let ret = HVReturnT::try_from(result).map_err(|e| {
                anyhow!(
                    "unexpected hv_return_t value {:#x} from hv_vcpu_run",
                    e as usize
                )
            })?;
            match ret {
                HVReturnT::HV_SUCCESS => {
                    let exit_t = self.exit_t();
                    match exit_t.decoded_syndrome.exception_class {
                        // HVC
                        0b010110 => {
                            let iss = exit_t.decoded_syndrome.iss as u16;
                            const NOOP: u8 = 0;
                            const HALT: u8 = 1;
                            const PRINT_U8: u8 = 2;
                            const PRINT_U64: u8 = 3;
                            const PANIC: u8 = 4;
                            match (iss >> 8) as u8 {
                                NOOP => {
                                    dbg!("NOOP");
                                },
                                HALT => {
                                    println!("halt received");
                                    return Ok(());
                                },
                                PRINT_U8 => {
                                    std::io::stdout().write_all(&[iss as u8]).unwrap();
                                }
                                PANIC => {
                                    panic!("panic in the guest")
                                },
                                other => {
                                    panic!("unsupported HVC value {:x}", other);
                                }
                            }
                        },
                        // some memory failure
                        0b100000 => {
                            println!("memory failure");
                        },
                        0b100100 => {
                            println!("data abort");
                        }
                        other => {
                            println!("unsupported exception class {:b}", other)
                        }
                    }
                    callback(Ok(self.exit_t())).unwrap();
                }
                err => {
                    let err1 = anyhow!("hv_vcpu_run() returned {:?}", err);
                    let err2 = anyhow!("hv_vcpu_run() returned {:?}", err);
                    callback(Err(err1)).unwrap();
                    return Err(err2);
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct Syndrome {
    exception_class: u8,
    is_32_bit_instruction: bool,
    iss: u32,
}

impl From<bindgen::hv_exception_syndrome_t> for Syndrome {
    fn from(s: bindgen::hv_exception_syndrome_t) -> Self {
        let s = s as u32;
        let eclass = (s >> 26) as u8;
        let is_32_bit = (s >> 25) & 1 == 1;
        let iss = s & 0xffffff;
        Self {
            exception_class: eclass,
            is_32_bit_instruction: is_32_bit,
            iss,
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
