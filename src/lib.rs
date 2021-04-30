use aarch64_debug::{DataAbortFlags, Syndrome};
use anyhow::{anyhow, bail, Context};
use bindgen_util::{assert_hv_return_t_ok, null_obj};
pub use bindgen_util::{HfVcpuExit, HvExitReason, HvMemoryFlags};
use elf_loader::LoadedElf;
use memory::GuestMemoryManager;
use std::thread::JoinHandle;
use std::{path::Path, sync::Arc};
pub use translation_table::{Granule, GRANULE_16K, GRANULE_4K};

use log::{debug, error, info, trace};

mod aarch64_debug;
mod addresses;
mod aligner;
mod bindgen_util;
mod elf_loader;
mod layout;
mod memory;
mod translation_table;

use addresses::{GuestIpaAddress, GuestVaAddress, Offset};
use layout::*;

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

pub struct HfVmBuilder<G> {
    entrypoint: Option<GuestVaAddress>,
    vbar_el1: Option<GuestVaAddress>,
    memory_manager: GuestMemoryManager<G>,
}

pub struct HfVm<G> {
    entrypoint: GuestVaAddress,
    vbar_el1: GuestVaAddress,
    memory_manager: Arc<GuestMemoryManager<G>>,
}

impl<G: Granule> HfVmBuilder<G> {
    pub fn new(granule: G) -> anyhow::Result<Self> {
        assert_hv_return_t_ok(unsafe { bindgen::hv_vm_create(null_obj()) }, "hv_vm_create")?;

        let ipa_start = DRAM_IPA_START;
        let va_start = DRAM_VA_START;
        let size = MEMORY_SIZE;
        debug!(
            "allocating guest memory, IPA start: {:x?}, size: {}",
            ipa_start.0, size
        );
        let memory_manager = GuestMemoryManager::new(granule, va_start, ipa_start, size)?;
        let vm = Self {
            memory_manager,
            entrypoint: None,
            vbar_el1: None,
        };
        vm.hf_map_memory(
            vm.memory_manager
                .get_memory_slice_by_ipa(ipa_start, size)?
                .as_mut_ptr(),
            ipa_start,
            size,
            HvMemoryFlags::ALL,
        )
        .context("error mapping DRAM memory into the guest VM")?;
        Ok(vm)
    }

    fn hf_map_memory(
        // void *addr, hv_ipa_t ipa, size_t size, hv_memory_flags_t flags
        &self,
        addr: *mut u8,
        ipa: GuestIpaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        if !aligner::ALIGNER_16K.is_aligned(addr as u64) {
            bail!("addr {:#x} is not aligned to page size", addr as u64)
        }
        if !aligner::ALIGNER_16K.is_aligned(ipa.0) {
            bail!("ipa {:#x} is not aligned to page size", ipa.0)
        }
        if !aligner::ALIGNER_16K.is_aligned(size as u64) {
            bail!("size {:#x} is not a multiple of page size", size)
        }

        debug!(
            "calling hv_vm_map: addr={:?}, ipa={:#x}, size={:?}, flags={:?}",
            addr, ipa.0, size, flags
        );

        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vm_map(addr as *mut _, ipa.0, size as u64, flags.bits() as u64) },
            "hv_vm_map",
        )
    }

    pub fn load_elf<P: AsRef<Path>>(&mut self, filename: P) -> anyhow::Result<LoadedElf> {
        let elf = self.memory_manager.load_elf(filename)?;
        self.entrypoint = Some(elf.entrypoint);
        self.vbar_el1 = Some(elf.vbar_el1);
        Ok(elf)
    }

    pub fn build(mut self) -> anyhow::Result<HfVm<G>> {
        let entrypoint = self.entrypoint.ok_or_else(|| {
            anyhow!("entrypoint not set, probably ELF not loaded, or loaded incorrectly")
        })?;
        let vbar_el1 = self.vbar_el1.ok_or_else(|| {
            anyhow!("vbar_el1 not set, probably ELF not loaded, or loaded incorrectly")
        })?;
        self.memory_manager
            .configure_dram()
            .context("error configuring DRAM")?;
        Ok(HfVm {
            entrypoint,
            vbar_el1,
            memory_manager: Arc::new(self.memory_manager),
        })
    }
}

impl<G: Granule + 'static> HfVm<G> {
    pub fn vcpu_create_and_run(
        &self,
        entrypoint: Option<GuestVaAddress>,
    ) -> anyhow::Result<JoinHandle<anyhow::Result<()>>> {
        let memory_manager = self.memory_manager.clone();
        let entrypoint = entrypoint.unwrap_or(self.entrypoint);

        let vbar_el1 = self.vbar_el1;
        let ttbr0 = memory_manager.get_ttbr_0();
        let ttbr1 = memory_manager.get_ttbr_1();

        Ok(std::thread::spawn(move || {
            let vcpu = VCpu::new(memory_manager).unwrap();
            let start_state = VcpuStartState {
                guest_pc: entrypoint,
                guest_vbar_el1: vbar_el1,
                ttbr0,
                ttbr1,
            };
            vcpu.simple_run_loop(start_state)
                .context("error calling simple_run_loop()")
        }))
    }
}

#[derive(Debug)]
pub struct VCpu<G> {
    id: u64,
    memory_manager: Arc<GuestMemoryManager<G>>,
    exit_t: *mut bindgen::hv_vcpu_exit_t,
    next_breakpoint: u16,
}

#[derive(Copy, Clone, Debug)]
struct VcpuStartState {
    guest_pc: GuestVaAddress,
    guest_vbar_el1: GuestVaAddress,
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
}

#[repr(C)]
struct StartParams {
    dram_start: GuestVaAddress,
    dram_usable_start: GuestVaAddress,
    dram_size: u64,
    log_level: u64,
}

impl<G: Granule> VCpu<G> {
    fn new(memory_manager: Arc<GuestMemoryManager<G>>) -> anyhow::Result<Self> {
        let mut vcpu = Self {
            id: 0,
            memory_manager,
            exit_t: core::ptr::null_mut(),
            next_breakpoint: 0,
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
    fn set_sys_reg<N: core::fmt::Display>(
        &mut self,
        reg: bindgen::hv_sys_reg_t,
        value: u64,
        name: N,
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

    fn get_feature_reg(&mut self, reg: bindgen::hv_feature_reg_t) -> anyhow::Result<u64> {
        let mut value = 0u64;
        assert_hv_return_t_ok(
            unsafe { bindgen::hv_vcpu_config_get_feature_reg(null_obj(), reg, &mut value) },
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
            ($reg:ident) => {{
                let value = self.get_sys_reg(bindgen::$reg)?;
                debug!("{}: {:#x}", &stringify!($reg)[24..], value);
                value
            }};
        }

        macro_rules! dump_feature_reg {
            ($reg:ident) => {
                debug!(
                    "{}: {:#x}",
                    &stringify!($reg)[32..],
                    self.get_feature_reg(bindgen::$reg)?
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
        let far_el1 = GuestVaAddress(dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_FAR_EL1));

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

        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_MDSCR_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_SPSR_EL1);

        dump_feature_reg!(hv_feature_reg_t_HV_FEATURE_REG_CTR_EL0);

        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_DBGBCR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_DBGBVR0_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_DBGBCR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_DBGBVR1_EL1);
        dump_sys_reg!(hv_sys_reg_t_HV_SYS_REG_MDSCR_EL1);

        let esr_el1 = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ESR_EL1)?;
        if esr_el1 != 0 {
            let syndrome = Syndrome::from(esr_el1);
            debug!("ESR EL1 decoded: {:#x?}", &syndrome);
            use aarch64_debug::*;
            match syndrome.exception_class {
                EXC_INSTR_ABORT_LOWER
                | EXC_INSTR_ABORT_SAME
                | EXC_DATA_ABORT_SAME
                | EXC_DATA_ABORT_LOWER => {
                    match self.memory_manager.simulate_address_lookup(far_el1) {
                        Ok(lookup) => match lookup {
                            Some(ipa) => info!("FAR_EL1 {:?} => {:?}", far_el1, ipa),
                            None => error!("didn't find IPA for FAR_EL1 {:?}", far_el1),
                        },
                        Err(e) => {
                            error!(
                                "error trying to simulate lookup of FAR_EL1 {:?}: {:?}",
                                far_el1, e
                            )
                        }
                    }
                }
                _ => {}
            }
        };
        Ok(())
    }

    fn print_stack(&mut self) -> anyhow::Result<()> {
        let sp = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SP_EL1)?;
        let len = self.get_stack_end().0 - sp;
        if len == 0 {
            debug!("STACK AT {:#x} is empty", sp);
            return Ok(());
        }
        debug!("STACK AT {:#x}, length {}", sp, len);

        let stack = self
            .memory_manager
            .get_memory_slice(GuestVaAddress(sp), len as usize)
            .with_context(|| anyhow!("error getting stack memory for stack at {:#x}", sp))?;

        hexdump::hexdump(&stack);
        Ok(())
    }

    fn get_stack_end(&self) -> GuestVaAddress {
        let dram_config = self.memory_manager.get_dram_config().unwrap();
        let size = dram_config.size - (STACK_SIZE * self.id);
        dram_config.start_va.add(Offset(size))
    }

    fn debug_data_abort(&mut self, iss: u32) -> anyhow::Result<()> {
        let dai = DataAbortFlags(iss);
        let write_value = match (dai.is_write(), dai.srt()) {
            (true, Some(srt)) => Some(self.get_reg(bindgen::hv_reg_t_HV_REG_X0 + (srt as u32))?),
            _ => None,
        };
        error!(
            "unhandled data abort: address={:#x?}, flags={:#?}, write_value={:#x?}",
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

        // Enable floating point
        {
            const FPEN_NO_TRAP: u64 = 0b11 << 20; // disable trapping of FP instructions
            const CPACR_EL1: u64 = FPEN_NO_TRAP;
            self.set_sys_reg(
                bindgen::hv_sys_reg_t_HV_SYS_REG_CPACR_EL1,
                CPACR_EL1,
                "CPACR_EL1",
            )?
        }

        // Enable EL1
        {
            // TODO: I do NOT understand why these are written to CPSR and they work
            // like if they were written to DAIF.
            // This piece is copied from libkrun's code.
            const PSR_MODE_EL1H: u64 = 0x0000_0005; // EL1
            const PSR_F_BIT: u64 = 1 << 6;
            const PSR_I_BIT: u64 = 1 << 7;
            const PSR_A_BIT: u64 = 1 << 8;

            #[allow(dead_code)]
            const PSR_D_BIT: u64 = 1 << 9; // bit 9
            #[allow(dead_code)]
            const PSR_D_BIT_DISABLE: u64 = 0;

            const PSTATE_FAULT_BITS_64: u64 = PSR_MODE_EL1H
                | PSR_A_BIT
                | PSR_F_BIT
                | PSR_I_BIT
                | PSR_D_BIT_DISABLE
                | PSR_MODE_EL1H;
            self.set_reg(bindgen::hv_reg_t_HV_REG_CPSR, PSTATE_FAULT_BITS_64, "CPSR")?;
            // self.set_sys_reg(
            //     bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1,
            //     PSTATE_FAULT_BITS_64,
            //     "SPSR_EL1",
            // )?;
        }

        {
            // Set all the required registers.
            {
                let mut tcr_el1 = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_TCR_EL1)?;

                tcr_el1 |= self.memory_manager.get_granule().tg0_bits()
                    | self.memory_manager.get_granule().tg1_bits()
                    | TCR_EL1_IPS
                    | self.memory_manager.get_txsz() as u64
                    | ((self.memory_manager.get_txsz() as u64) << 16)
                    | TCR_EL1_HA
                    | TCR_EL1_HD;
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
        };

        {
            let dram_config = self.memory_manager.get_dram_config().unwrap();
            let start_params_va = dram_config.start_va;
            let usable_memory_start =
                start_params_va.add(Offset(core::mem::size_of::<StartParams>() as u64));

            let start_params = StartParams {
                dram_start: self.memory_manager.get_va(Offset(0)),
                dram_usable_start: usable_memory_start,
                dram_size: self.memory_manager.get_size() as u64,
                log_level: match std::env::var("ARMOS_LOG")
                    .map(|s| s.to_lowercase())
                    .as_deref()
                    .unwrap_or_default()
                {
                    "trace" => 0,
                    "debug" => 1,
                    "info" => 2,
                    "warn" => 3,
                    "error" => 4,
                    _ => 2,
                },
            };
            let start_params_mem = self
                .memory_manager
                .get_memory_slice(start_params_va, core::mem::size_of::<StartParams>())
                .with_context(|| {
                    format!(
                        "error getting start_params memory at {:#x?}",
                        start_params_va.0
                    )
                })?;
            unsafe {
                core::ptr::copy(
                    &start_params,
                    start_params_mem.as_ptr() as *mut StartParams,
                    1,
                )
            };
            self.set_reg(bindgen::hv_reg_t_HV_REG_X0, start_params_va.0, "X0")?;
        }

        // Uncomment to be able to "step" through the code.
        // The code for it is not implemented yet, and if just ran like this, it loops forever on LDXR/STXR pairs,
        // so those instructions can't be debugged.
        // However with some manual tinkering you can
        //

        // self.enable_soft_debug()?;
        self.spawn_cancel_thread();
        // self.set_pending_irq()?;

        self.set_sys_reg(
            bindgen::hv_sys_reg_t_HV_SYS_REG_VBAR_EL1,
            start_state.guest_vbar_el1.0,
            "VBAR_EL1",
        )?;

        // These breakpoints don't work :(
        self.add_breakpoint(start_state.guest_pc)?;

        // self.enable_soft_debug()?;

        let run = |vcpu: &mut VCpu<G>| loop {
            assert_hv_return_t_ok(unsafe { bindgen::hv_vcpu_run(vcpu.id) }, "hv_vcpu_run")?;

            let exit_t = vcpu.exit_t();
            if exit_t.reason != HvExitReason::HV_EXIT_REASON_EXCEPTION {
                vcpu.dump_all_registers()?;
                panic!("unexpected exit reason {:?}", exit_t.reason);
            }

            match exit_t.reason {
                HvExitReason::HV_EXIT_REASON_EXCEPTION => {}
                other => bail!("unsupported HvExitReason {:?}", other),
            };

            assert_eq!(exit_t.reason, HvExitReason::HV_EXIT_REASON_EXCEPTION);

            use aarch64_debug as ad;

            match exit_t.decoded_syndrome.exception_class {
                ad::EXC_HVC => {
                    let iss = exit_t.decoded_syndrome.iss as u16;
                    const NOOP: u8 = 0;
                    const HALT: u8 = 1;
                    const PANIC: u8 = 4;
                    const EXCEPTION: u8 = 5;
                    const SYNCHRONOUS_EXCEPTION: u8 = 6;
                    const PRINT_STRING: u8 = 7;
                    const IRQ: u8 = 8;

                    trace!("received HVC event {}", iss);
                    match iss as u8 {
                        NOOP => {
                            debug!("NOOP HVC received");
                        }
                        HALT => {
                            info!("halt received");
                            vcpu.dump_all_registers()?;
                            return Ok(());
                        }
                        PANIC => {
                            vcpu.dump_all_registers()?;
                            bail!("guest panicked");
                        }
                        EXCEPTION | SYNCHRONOUS_EXCEPTION | IRQ => {
                            let mut name = match iss as u8 {
                                EXCEPTION => "unknown",
                                SYNCHRONOUS_EXCEPTION => "synchronous",
                                IRQ => "IRQ",
                                _ => unreachable!(),
                            };
                            let el1_syndrome = Syndrome::from(
                                vcpu.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ESR_EL1)?,
                            );

                            match el1_syndrome.exception_class {
                                ad::EXC_DATA_ABORT_SAME => {
                                    vcpu.debug_data_abort(el1_syndrome.iss)?;
                                    name = "data abort";
                                }
                                ad::EXC_SOFT_STEP_SAME | ad::EXC_BREAKPOINT_SAME => {
                                    let instruction_address =
                                        vcpu.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ELR_EL1)?;
                                    trace!(
                                        "Debug exception, address {:#x?}, continuing",
                                        instruction_address
                                    );
                                    let spsr_el1 = vcpu
                                        .get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1)?;
                                    // Set pstate.SS to 1, so that it actually executes the next instruction.
                                    vcpu.set_sys_reg(
                                        bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1,
                                        spsr_el1 | (1 << 21),
                                        "SPSR_EL1",
                                    )?;
                                    continue;
                                }
                                _ => {
                                    error!(
                                        "exception class unknown. Full syndrome: {:#x?}",
                                        el1_syndrome
                                    );
                                }
                            }
                            vcpu.dump_all_registers()?;
                            vcpu.print_stack()?;
                            bail!("HVC EL1 -> EL1 exception: {}", name);
                        }
                        PRINT_STRING => {
                            let addr = vcpu.get_reg(bindgen::hv_reg_t_HV_REG_X0)?;
                            let len = vcpu.get_reg(bindgen::hv_reg_t_HV_REG_X1)?;

                            let slice = vcpu
                                .memory_manager
                                .get_memory_slice(GuestVaAddress(addr), len as usize)
                                .with_context(|| {
                                    format!("error getting guest memory, address {:#x?}", addr)
                                })
                                .context("error processing PRINT_STRING hvc event")?;
                            let value = core::str::from_utf8(slice).context(
                                "error converting string from PRINT_STRING event to UTF-8",
                            )?;
                            print!("{}", value);
                        }
                        other => {
                            bail!("unsupported HVC value {:x}", other);
                        }
                    }
                }
                ad::EXC_INSTR_ABORT_LOWER => {
                    error!("instruction abort");
                    vcpu.dump_all_registers()?;
                    vcpu.print_stack()?;
                    error!("{:#x?}", vcpu.exit_t());
                    bail!("instruction abort");
                }
                ad::EXC_SOFT_STEP_LOWER => {
                    let instruction_ipa = exit_t.exception.virtual_address;
                    trace!(
                        "Debug exception, IPA address {:#x?}, continuing",
                        instruction_ipa
                    );
                    let spsr_el1 = vcpu.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1)?;
                    // Set pstate.SS to 1, so that it actually executes the next instruction.
                    vcpu.set_sys_reg(
                        bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1,
                        spsr_el1 | (1 << 21),
                        "SPSR_EL1",
                    )?;
                    continue;
                }
                ad::EXC_DATA_ABORT_LOWER => {
                    vcpu.debug_data_abort(vcpu.exit_t().decoded_syndrome.iss)?;
                    bail!("data abort EL1 -> EL2");
                }
                _ => {
                    bail!(
                        "unsupported exception class {:#x?}",
                        exit_t.decoded_syndrome
                    )
                }
            }
        };

        match run(&mut self) {
            Ok(_) => Ok(()),
            Err(err) => {
                error!("error running vcpu: {}. Dumping all registers.", &err);
                self.dump_all_registers()?;
                Err(err)
            }
        }
    }

    #[allow(dead_code)]
    fn set_pending_irq(&mut self) -> anyhow::Result<()> {
        assert_hv_return_t_ok(
            unsafe {
                bindgen::hv_vcpu_set_pending_interrupt(
                    self.id,
                    bindgen::hv_interrupt_type_t_HV_INTERRUPT_TYPE_IRQ,
                    true,
                )
            },
            "hv_vcpu_set_pending_interrupt",
        )?;
        Ok(())
    }

    #[allow(dead_code)]
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

    #[allow(dead_code)]
    fn add_breakpoint(&mut self, addr: GuestVaAddress) -> anyhow::Result<()> {
        let reg = self.next_breakpoint;
        use bindgen::*;
        use paste::paste;

        // Generates a long match statement, a little shorter than pasting the whole thing here.
        // Uses paste crate to concatenate tokens into an identifier.
        macro_rules! rmatch {
            ($($reg_number:tt),+) => {
                match reg {
                    $($reg_number => (
                        paste!([<hv_sys_reg_t_HV_SYS_REG_DBGBCR $reg_number _EL1>]),
                        paste!([<hv_sys_reg_t_HV_SYS_REG_DBGBVR $reg_number _EL1>]),
                    )),+,
                    _ => bail!("no more hardware breakpoints available")
                }
            }
        }
        let (ctrl_reg, value_reg) = rmatch!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);

        let mut ctrl_reg_value: u64 = 0b0000 << 20; // breakpoint type 0 - unlinked address match.

        // This is unneeded actually, as for Aarch64 the bas field is reserved, but whatever.
        ctrl_reg_value |= 0b1111 << 5; // BAS - for A64 instructions.

        ctrl_reg_value |= 0b11 << 1; // PMC - to enable EL1 breakpoints.

        // ctrl_reg_value |= 0b01 << 14; // SSC
        ctrl_reg_value |= 1; // enable

        self.set_sys_reg(ctrl_reg, ctrl_reg_value, format_args!("DBGBCR{}_EL1", reg))?;
        self.set_sys_reg(value_reg, addr.0, format_args!("DBGBVR{}_EL1", reg))?;

        // If this is the first breakpoint used, setup the control register.
        if reg == 0 {
            let mut mdscr = self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_MDSCR_EL1)?;
            mdscr |= 1 << 13; // KDE bit
            mdscr |= 1 << 15; // MDE bit
            self.set_sys_reg(
                bindgen::hv_sys_reg_t_HV_SYS_REG_MDSCR_EL1,
                mdscr,
                "MDSCR_EL1",
            )?;

            // Trap to the host.
            // assert_hv_return_t_ok(
            //     unsafe { bindgen::hv_vcpu_set_trap_debug_exceptions(self.id, true) },
            //     "hv_vcpu_set_trap_debug_exceptions",
            // )?;
        }
        self.next_breakpoint += 1;
        Ok(())
    }

    #[allow(dead_code)]
    fn enable_soft_debug(&mut self) -> anyhow::Result<()> {
        // Soft debug
        const KDE: u64 = 1 << 13;
        const SOFTWARE_STEP_ENABLE: u64 = 1;
        let mdscr_el1 = KDE | SOFTWARE_STEP_ENABLE;

        self.set_sys_reg(
            bindgen::hv_sys_reg_t_HV_SYS_REG_MDSCR_EL1,
            mdscr_el1,
            "MDSCR_EL1",
        )?;

        // self.set_sys_reg(
        //     bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1,
        //     1 << 21,
        //     "SPSR_EL1",
        // )?;

        // assert_hv_return_t_ok(
        //     unsafe { bindgen::hv_vcpu_set_trap_debug_exceptions(self.id, true) },
        //     "hv_vcpu_set_trap_debug_exceptions",
        // )?;
        Ok(())
    }
}
