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
    Bytes, GuestAddress, GuestMemory, GuestMemoryMmap, GuestMemoryRegion,
    MemoryRegionAddress,
};

// mod page_table;

pub fn get_page_size() -> u64 {
    unsafe { libc::sysconf(libc::_SC_PAGE_SIZE) as u64}
}

pub fn is_aligned_to_page_size(value: u64) -> bool {
    align_down_to_page_size(value) == value
}

pub fn align_down_to_page_size(value: u64) -> u64 {
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
}

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: GuestAddress,
}

pub const DRAM_MEM_START: u64 = 0x8000_0000; // 2 GB.
                                             // This is bad, but seems to fuck up without a page table if set to higher, as the executable is not a PIE one.
                                             // pub const EXEC_START: usize = 0x2000_0000; // 512 MB,
pub const EXEC_START: u64 = 0x20_0000; // This should be able to map the executable we have.

pub const EXEC_MEM_SIZE: usize = 16 * 1024 * 1024;

// this could be configurable, it's just that we don't care yet.
pub const MEMORY_SIZE: usize = 32 * 1024 * 1024;

pub const STACK_SIZE: u64 = 1024 * 1024;
pub const STACK_END: u64 = DRAM_MEM_START + STACK_SIZE;

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
        let memory = GuestMemoryMmap::from_ranges(&[
            (GuestAddress(EXEC_START as u64), EXEC_MEM_SIZE),
            (GuestAddress(DRAM_MEM_START as u64), MEMORY_SIZE),
        ])?;
        let vm = Self {
            memory: Arc::new(memory),
        };
        vm.memory.with_regions(|_, region| -> anyhow::Result<()> {
            let host_addr = region.get_host_address(MemoryRegionAddress(0))?;
            vm.map_memory(
                host_addr,
                region.start_addr(),
                region.size(),
                HvMemoryFlags::ALL,
            )?;
            Ok(())
        })?;
        Ok(vm)
    }

    pub fn get_memory(&self) -> Arc<GuestMemoryMmap> {
        self.memory.clone()
    }

    fn map_memory(
        // void *addr, hv_ipa_t ipa, size_t size, hv_memory_flags_t flags
        &self,
        addr: *mut u8,
        ipa: GuestAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        if !is_aligned_to_page_size(addr as u64) {
            bail!("addr {:x} is not aligned to page size", addr as u64)
        }
        if !is_aligned_to_page_size(ipa.0) {
            bail!("ipa {:x} is not aligned to page size", ipa.0)
        }
        if !is_aligned_to_page_size(size as u64) {
            bail!("size {:x} is not a multiple of page size", size)
        }

        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vm_map(addr as *mut _, ipa.0, size as u64, flags.bits() as u64) },
            "hv_vm_map",
        )
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P) -> anyhow::Result<LoadedElf> {
        let file = std::fs::File::open(filename)?;
        let map = unsafe { memmap::MmapOptions::default().map(&file) }?;
        let obj = object::File::parse(&map)?;
        use object::read::ObjectSection;
        use object::Object;

        let result = LoadedElf {
            entrypoint: GuestAddress(obj.entry()),
        };

        // let mut min_address = u64::MAX;
        // let mut max_address = u64::MIN;

        for section in obj.sections() {
            use object::SectionKind::*;
            match section.kind() {
                Text | Data | ReadOnlyData => {
                    let data = section.data()?;
                    let slice = self
                        .memory
                        .get_slice(GuestAddress(section.address()), section.size() as usize)?;
                    slice.copy_from(data);
                }
                _ => {}
            }
        }

        // println!("Min addr: {:x}, max addr: {:x}", min_address, max_address);

        // let mut mmap = memmap::MmapOptions::default().len(max_address - min_address).map_anon()?;
        // for section in obj.sections() {
        //     use object::SectionKind::*;
        //     match section.kind() {
        //         Text | Data | ReadOnlyData => {
        //             let offset = section.address() as usize - min_address;
        //             let data = &mut mmap.as_mut()[offset..offset + section.size() as usize];
        //             data.copy_from_slice(section.data().unwrap());
        //         },
        //         other => {
        //             println!("ignoring section {:?} with kind {:?}", section.name(), other);
        //         }
        //     }
        // }

        // self.memory.get_host_address(addr)

        // self.map_memory(mmap.as_ptr().into(), (offset + min_address).into(), mmap.len(), HvMemoryFlags::ALL)?;
        // result.maps.push(mmap);

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

    pub fn vcpu_create_and_run(
        &mut self,
        memory: Arc<GuestMemoryMmap>,
        entrypoint: GuestAddress,
    ) -> JoinHandle<anyhow::Result<()>> {
        std::thread::spawn(move || {
            let vcpu = VCpu::new(memory).unwrap();
            let start_state = VcpuStartState {
                guest_pc: entrypoint,
            };
            vcpu.simple_run_loop(start_state)
        })
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

struct VcpuStartState {
    guest_pc: GuestAddress,
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
    fn set_reg(&mut self, reg: bindgen::hv_reg_t, value: u64) -> anyhow::Result<()> {
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_set_reg(self.id, reg, value) },
            "hv_vcpu_set_reg",
        )
    }
    fn set_sys_reg(&mut self, reg: bindgen::hv_sys_reg_t, value: u64) -> anyhow::Result<()> {
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
                println!("{}: {:#x}", stringify!($reg), self.get_reg(bindgen::$reg)?);
            };
        }

        macro_rules! dump_sys_reg {
            ($reg:ident) => {
                println!(
                    "{}: {:#x}",
                    stringify!($reg),
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
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ID_AA64MMFR2_EL1);

        // FP state
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_CPACR_EL1);

        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_ESR_EL1);

        Ok(())
    }

    fn print_stack(&mut self) -> anyhow::Result<()> {
        let sp = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SP_EL1)?;
        let len = self.get_stack_end() - sp;
        let mut data = vec![0u8; len as usize];
        println!("STACK AT {:#x}, length {}", sp, len);
        self.memory.read_slice(&mut data, GuestAddress(sp))?;
        hexdump::hexdump(&data);
        Ok(())
    }

    fn get_stack_end(&self) -> u64 {
        DRAM_MEM_START + MEMORY_SIZE as u64 - STACK_SIZE * self.id
    }

    fn simple_run_loop(mut self, start_state: VcpuStartState) -> anyhow::Result<()> {
        self.set_sys_reg(
            bindgen::hv_sys_reg_t_HV_SYS_REG_SP_EL1,
            self.get_stack_end(),
        )
        .context("failed setting stack pointer")?;
        self.set_reg(bindgen::hv_reg_t_HV_REG_PC, start_state.guest_pc.0)
            .context("failed setting initial program counter")?;

        self.set_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_VBAR_EL1, 0x40_0000)
            .context("failed setting VBAR")?;

        {
            // Enable floating point
            const FPEN_NO_TRAP: u64 = 0b11 << 20; // disable trapping of FP instructions
            const CPACR_EL1: u64 = FPEN_NO_TRAP;
            self.set_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_CPACR_EL1, CPACR_EL1)?
        }

        {
            // Setup translation tables

            // const TG0_GRANULE_16K: u64 = 1 << 15;
            // self.set_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_TTBR0_EL1, TG0_GRANULE_16K)?;

            // TODO: setup T0SZ to 16, so that all 4 levels are used.
            // Or honestly a little more, so that 3 levels are used, as 4th only supports 1 bit of lookup - i.e. 2 values in the table.

            // TODO: Look up these bits, they are used  The TCR_ELx.{SH0, ORGN0, IRGN0}

            // TODO: If the Effective value of TCR_ELx.DS is 1, block descriptors are not supported.
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
        self.set_reg(bindgen::hv_reg_t_HV_REG_CPSR, PSTATE_FAULT_BITS_64)
            .unwrap();

        loop {
            assert_hv_return_t_ok(unsafe { bindgen::hv_vcpu_run(self.id) }, "hv_vcpu_run")?;

            let exit_t = self.exit_t();
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
                            dbg!("NOOP");
                        }
                        HALT => {
                            println!("halt received");
                            return Ok(());
                        }
                        PANIC => {
                            panic!("panic in the guest")
                        }
                        EXCEPTION | SYNCHRONOUS_EXCEPTION | IRQ => {
                            let name = match iss as u8 {
                                EXCEPTION => "exception",
                                SYNCHRONOUS_EXCEPTION => "synchronous exception",
                                _ => unreachable!(),
                            };
                            let el1_syndrome = Syndrome::from(
                                self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ESR_EL1)?,
                            );
                            println!("{}. Decoded ESR_EL1: {:#x?}", name, el1_syndrome);

                            self.dump_all_registers()?;
                            self.print_stack()?;
                            panic!("{}", name);
                        }
                        PRINT_STRING => {
                            let addr = self.get_reg(bindgen::hv_reg_t_HV_REG_X0)?;
                            let len = self.get_reg(bindgen::hv_reg_t_HV_REG_X1)?;
                            let slice = self.memory.get_slice(GuestAddress(addr), len as usize)?;
                            let slice = unsafe {
                                core::slice::from_raw_parts(slice.as_ptr(), len as usize)
                            };
                            println!("{}", core::str::from_utf8(slice)?);
                        }
                        other => {
                            panic!("unsupported HVC value {:x}", other);
                        }
                    }
                }
                // some memory failure
                0b100000 => {
                    println!("memory failure");
                }
                0b100100 => {
                    println!("data abort");
                }
                other => {
                    println!("unsupported exception class {:b}", other)
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct Syndrome {
    exception_class: u8,
    iss: u32,
    original_value: u64,
}

impl From<u64> for Syndrome {
    fn from(s: u64) -> Self {
        let orig = s;
        let s = s as u32;
        let eclass = ((s >> 26) & 0b111111) as u8;
        let iss = s & 0xffffff;
        Self {
            exception_class: eclass,
            iss,
            original_value: orig,
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
