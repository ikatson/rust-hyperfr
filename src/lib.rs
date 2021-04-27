use aarch64_debug::{DataAbortFlags, Syndrome};
use anyhow::{anyhow, bail, Context};
use bindgen_util::{assert_hv_return_t_ok, null_obj};
pub use bindgen_util::{HfVcpuExit, HvExitReason, HvMemoryFlags};
use std::sync::Arc;
use std::thread::JoinHandle;
use vm_memory::{GuestMemory, GuestMemoryMmap};

use log::{debug, error, info, trace};

pub mod aarch64_debug;
pub mod addresses;
pub mod aligner;
mod bindgen_util;
mod elf_loading;
pub mod layout;
pub mod page_table;

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

#[derive(Debug)]
pub struct GuestMemoryManager {
    memory: Arc<GuestMemoryMmap>,
}

pub struct HfVmBuilder {
    entrypoint: Option<GuestVaAddress>,
    vbar_el1: Option<GuestVaAddress>,
    memory_manager: GuestMemoryManager,
}

pub struct HfVm {
    entrypoint: GuestVaAddress,
    vbar_el1: GuestVaAddress,
    memory_manager: Arc<GuestMemoryManager>,
}

impl GuestMemoryManager {
    pub fn new() -> anyhow::Result<Self> {
        let memory = Arc::new(
            GuestMemoryMmap::from_ranges(&[(DRAM_IPA_START.as_guest_address(), MEMORY_SIZE)])
                .context("error allocating guest memory")?,
        );

        let mut mm = Self { memory };

        {
            let ipa = DRAM_IPA_START.add(DRAM_KERNEL_USABLE_DRAM_OFFSET);
            let va = DRAM_VA_START.add(DRAM_KERNEL_USABLE_DRAM_OFFSET);
            let usable_memory_size =
                (MEMORY_SIZE as u64 - DRAM_KERNEL_USABLE_DRAM_OFFSET.0) as usize;
            // This is the RAM that the kernel is free to use for whatever purpose, e.g. allocating.
            debug!(
                "configuring translation tables for DRAM, ipa {:#x?}, va {:#x?}, usable memory size {}",
                ipa.0, va.0, usable_memory_size,
            );

            mm.configure_page_tables(ipa, va, usable_memory_size, HvMemoryFlags::ALL)
                .context("error configuring page tables for DRAM")?;
        }

        Ok(mm)
    }
    fn get_ttbr_0_dram_offset(&self) -> Offset {
        DRAM_TTBR_OFFSET
    }

    fn get_ttbr_1_dram_offset(&self) -> Offset {
        self.get_ttbr_0_dram_offset().add(Offset(TTBR_SIZE as u64))
    }

    unsafe fn get_memory_slice(
        &self,
        va: GuestVaAddress,
        size: usize,
    ) -> anyhow::Result<&mut [u8]> {
        let ipa = self
            .simulate_address_lookup(va)?
            .ok_or_else(|| anyhow!("cannot find address {:#x?} in translation tables", va.0))?;
        let vslice = self.memory.get_slice(ipa.as_guest_address(), size)?;
        let ptr = vslice.as_ptr();
        Ok(core::slice::from_raw_parts_mut(ptr, size))
    }

    unsafe fn get_translation_table_for_va_ptr(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<(GuestIpaAddress, *mut page_table::TranslationTableLevel2_16k)> {
        let top_bit_set = (va.0 >> 55) & 1 == 1;

        let table_start_dram_offset = if top_bit_set {
            self.get_ttbr_1_dram_offset()
        } else {
            self.get_ttbr_0_dram_offset()
        };

        let table_ipa = DRAM_IPA_START.add(table_start_dram_offset);
        let table_ptr = self
            .memory
            .get_slice(table_ipa.as_guest_address(), TTBR_SIZE)
            .with_context(|| format!("error getting slice of memory at {:#x?}", table_ipa.0))?
            .as_ptr() as *mut page_table::TranslationTableLevel2_16k;
        Ok((table_ipa, table_ptr))
    }

    fn get_translation_table_for_va_mut(
        &mut self,
        va: GuestVaAddress,
    ) -> anyhow::Result<(GuestIpaAddress, &mut page_table::TranslationTableLevel2_16k)> {
        unsafe {
            let (ipa, t) = self.get_translation_table_for_va_ptr(va)?;
            Ok((ipa, &mut *t as _))
        }
    }

    fn get_translation_table_for_va(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<(GuestIpaAddress, &page_table::TranslationTableLevel2_16k)> {
        unsafe {
            let (ipa, t) = self.get_translation_table_for_va_ptr(va)?;
            Ok((ipa, &*t as _))
        }
    }

    pub fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>> {
        let (ipa, table) = self.get_translation_table_for_va(va)?;
        Ok(table.simulate_lookup(ipa, va))
    }

    fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()> {
        let (table_ipa, table) = self.get_translation_table_for_va_mut(va)?;

        table
            .setup(table_ipa, va, ipa, size, flags)
            .context("error configuring the Level 2 translation table")?;
        Ok(())
    }
}

impl HfVmBuilder {
    pub fn new() -> anyhow::Result<Self> {
        assert_hv_return_t_ok(unsafe { bindgen::hv_vm_create(null_obj()) }, "hv_vm_create")?;
        debug!(
            "allocating guest memory, IPA start: {:x?}, size: {}",
            DRAM_IPA_START.0, MEMORY_SIZE
        );
        let memory_manager = GuestMemoryManager::new()?;
        let vm = Self {
            memory_manager,
            entrypoint: None,
            vbar_el1: None,
        };
        vm.hf_map_memory(
            vm.memory_manager
                .memory
                .get_host_address(DRAM_IPA_START.as_guest_address())
                .context("error getting host address for guest memory start")?,
            DRAM_IPA_START,
            MEMORY_SIZE,
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

    pub fn build(self) -> anyhow::Result<HfVm> {
        let entrypoint = self.entrypoint.ok_or_else(|| {
            anyhow!("entrypoint not set, probably ELF not loaded, or loaded incorrectly")
        })?;
        let vbar_el1 = self.vbar_el1.ok_or_else(|| {
            anyhow!("vbar_el1 not set, probably ELF not loaded, or loaded incorrectly")
        })?;
        Ok(HfVm {
            entrypoint,
            vbar_el1,
            memory_manager: Arc::new(self.memory_manager),
        })
    }
}

impl HfVm {
    pub fn vcpu_create_and_run(
        &self,
        entrypoint: Option<GuestVaAddress>,
    ) -> anyhow::Result<JoinHandle<anyhow::Result<()>>> {
        let memory_manager = self.memory_manager.clone();
        let entrypoint = entrypoint.unwrap_or(self.entrypoint);

        let vbar_el1 = self.vbar_el1;
        let ttbr0 = DRAM_IPA_START.add(memory_manager.get_ttbr_0_dram_offset());
        let ttbr1 = DRAM_IPA_START.add(memory_manager.get_ttbr_1_dram_offset());

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
pub struct VCpu {
    id: u64,
    memory_manager: Arc<GuestMemoryManager>,
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

impl VCpu {
    fn new(memory_manager: Arc<GuestMemoryManager>) -> anyhow::Result<Self> {
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
            ($reg:ident) => {
                debug!(
                    "{}: {:#x}",
                    &stringify!($reg)[24..],
                    self.get_sys_reg(bindgen::$reg)?
                );
            };
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
            debug!("ESR EL1 decoded: {:#x?}", Syndrome::from(esr_el1));
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

        let stack = unsafe {
            self.memory_manager
                .get_memory_slice(GuestVaAddress(sp), len as usize)
                .with_context(|| anyhow!("error getting stack memory for stack at {:#x}", sp))?
        };

        hexdump::hexdump(&stack);
        Ok(())
    }

    fn get_stack_end(&self) -> GuestVaAddress {
        STACK_END.checked_sub(Offset(STACK_SIZE * self.id)).unwrap()
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

                tcr_el1 |= TCR_EL1_TG0_GRANULE
                    | TCR_EL1_TG1_GRANULE
                    | TCR_EL1_IPS
                    | TCR_EL1_T0SZ
                    | TCR_EL1_T1SZ
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
            let start_params_dram_offset = DRAM_KERNEL_USABLE_DRAM_OFFSET;
            let start_params_end_offset =
                start_params_dram_offset.add(Offset(core::mem::size_of::<StartParams>() as u64));

            let start_params = StartParams {
                dram_start: DRAM_VA_START,
                dram_usable_start: DRAM_VA_START.add(start_params_end_offset),
                dram_size: MEMORY_SIZE as u64,
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
            let start_params_ipa = DRAM_IPA_START.add(start_params_dram_offset);
            let start_params_mem = self
                .memory_manager
                .memory
                .get_slice(
                    start_params_ipa.as_guest_address(),
                    core::mem::size_of::<StartParams>(),
                )
                .with_context(|| {
                    format!(
                        "error getting start_params memory at {:#x?}",
                        start_params_ipa.0
                    )
                })?;
            unsafe {
                core::ptr::copy(
                    &start_params,
                    start_params_mem.as_ptr() as *mut StartParams,
                    1,
                )
            };
            self.set_reg(
                bindgen::hv_reg_t_HV_REG_X0,
                DRAM_VA_START.add(start_params_dram_offset).0,
                "X0",
            )?;
        }

        // Uncomment to be able to "step" through the code.
        // The code for it is not implemented yet, and if just ran like this, it loops forever on LDXR/STXR pairs,
        // so those instructions can't be debugged.
        // However with some manual tinkering you can
        //

        // self.enable_soft_debug()?;
        // self.spawn_cancel_thread();
        // self.set_pending_irq()?;

        self.set_sys_reg(
            bindgen::hv_sys_reg_t_HV_SYS_REG_VBAR_EL1,
            start_state.guest_vbar_el1.0,
            "VBAR_EL1",
        )?;

        // These breakpoints don't work :(
        self.add_breakpoint(start_state.guest_pc)?;

        // self.enable_soft_debug()?;

        let run = |vcpu: &mut VCpu| loop {
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

                            let slice = unsafe {
                                vcpu.memory_manager
                                    .get_memory_slice(GuestVaAddress(addr), len as usize)
                            }
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
