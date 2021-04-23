use anyhow::{anyhow, bail, Context};
use bindgen::{hv_exit_reason_t, NSObject};
use bitflags::bitflags;
use std::sync::Arc;
use std::{
    convert::{TryFrom, TryInto},
    path::Path,
    thread::JoinHandle,
};
use vm_memory::{GuestAddress, GuestMemory, GuestMemoryMmap};

use log::{debug, error, info, trace};

#[derive(Copy, Clone, Debug)]
pub struct GuestIpaAddress(u64);
impl GuestIpaAddress {
    const fn add(&self, offset: Offset) -> GuestIpaAddress {
        GuestIpaAddress(self.0 + offset.0)
    }
    const fn as_guest_address(&self) -> GuestAddress {
        GuestAddress(self.0)
    }
}

#[derive(Copy, Clone, Default, Debug)]
pub struct GuestVaAddress(u64);
impl GuestVaAddress {
    const fn add(&self, offset: Offset) -> GuestVaAddress {
        GuestVaAddress(self.0 + offset.0)
    }

    fn checked_sub(&self, offset: Offset) -> Option<GuestVaAddress> {
        self.0.checked_sub(offset.0).map(GuestVaAddress)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Offset(u64);
impl Offset {
    const fn add(&self, offset: Offset) -> Offset {
        Offset(self.0 + offset.0)
    }
}

pub mod page_table;

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

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: GuestVaAddress,
}

// Memory structure:
// VA_START - the virtual memory of the kernel so that it's in TTBR1.
// At that address we load the kernel itself, including exception vector table.
// VA_START + 1GB = DRAM

pub const VA_PAGE: u64 = 1 << 14;

pub const DRAM_IPA_START: GuestIpaAddress = GuestIpaAddress(0x80_0000);
pub const VA_START: GuestVaAddress = GuestVaAddress(0xffff_fff0_0000_0000);
pub const DRAM_VA_START: GuestVaAddress = VA_START.add(Offset(DRAM_IPA_START.0));

pub const KERNEL_BINARY_MEMORY_MAX_SIZE: u64 = 8 * 1024 * 1024; // 8 Mib

pub const DRAM_KERNEL_BINARY_OFFSET: Offset = Offset(0);

pub const DRAM_TTBR_OFFSET: Offset = DRAM_KERNEL_BINARY_OFFSET
    .add(Offset(KERNEL_BINARY_MEMORY_MAX_SIZE))
    .add(Offset(VA_PAGE));

pub const TTBR_SIZE: usize = core::mem::size_of::<page_table::TranslationTableLevel2_16k>();

pub const DRAM_KERNEL_USABLE_DRAM_OFFSET: Offset = DRAM_TTBR_OFFSET
    .add(Offset(TTBR_SIZE as u64 * 2))
    .add(Offset(VA_PAGE));

// this could be configurable, it's just that we don't care yet.
// This is 32 MiB, we just don't need more.
pub const MEMORY_SIZE: usize = 256 * 1024 * 1024;

pub const STACK_SIZE: u64 = 1024 * 1024;
pub const STACK_END: GuestVaAddress = DRAM_VA_START.add(Offset(MEMORY_SIZE as u64));

pub const TXSZ: u64 = 28;
pub const VA_REGION_SIZE: u64 = 1 << (64 - TXSZ); // The region size for virtual addresses.
pub const IPS_SIZE: u64 = 1 << 36; // 64 GB address size

pub const TCR_EL1_TG0_GRANULE: u64 = 0b10 << 14;
pub const TCR_EL1_TG1_GRANULE: u64 = 0b01 << 30;
pub const TCR_EL1_IPS: u64 = 0b001 << 32; // 64 GB
pub const TCR_EL1_T0SZ: u64 = TXSZ; // so that 36 bits remains.
pub const TCR_EL1_T1SZ: u64 = TXSZ << 16;
pub const TCR_EL1_HA: u64 = 1 << 39;
pub const TCR_EL1_HD: u64 = 1 << 40;

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

impl GuestMemoryManager {
    pub fn new() -> anyhow::Result<Self> {
        let memory = Arc::new(
            GuestMemoryMmap::from_ranges(&[(DRAM_IPA_START.as_guest_address(), MEMORY_SIZE)])
                .context("error allocating guest memory")?,
        );

        let mut mm = Self { memory };

        mm.initial_configure_page_tables_l2()
            .context("error in initial page table configuration")?;

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

    unsafe fn get_memory_slice(&self, va: GuestVaAddress, size: usize) -> anyhow::Result<&[u8]> {
        let ipa = self
            .simulate_address_lookup(va)?
            .ok_or_else(|| anyhow!("cannot find address {:#x?} in translation tables", va.0))?;
        let vslice = self.memory.get_slice(ipa.as_guest_address(), size)?;
        let ptr = vslice.as_ptr();
        Ok(core::slice::from_raw_parts(ptr, size))
    }

    fn initial_configure_page_tables_l2(&mut self) -> anyhow::Result<()> {
        for table_start_dram_offset in
            (&[self.get_ttbr_0_dram_offset(), self.get_ttbr_1_dram_offset()])
                .iter()
                .copied()
        {
            let page_table_guest_ipa = DRAM_IPA_START.add(table_start_dram_offset);
            let page_table_ptr =
                self.memory
                    .get_slice(page_table_guest_ipa.as_guest_address(), TTBR_SIZE)
                    .with_context(|| {
                        format!(
                            "error getting slice of memory at {:#x?}, size {}",
                            page_table_guest_ipa.0, TTBR_SIZE
                        )
                    })?
                    .as_ptr() as *mut page_table::TranslationTableLevel2_16k;

            let table =
                unsafe { &mut *page_table_ptr as &mut page_table::TranslationTableLevel2_16k };
            table
                .setup_l2(page_table_guest_ipa)
                .context("error setting up L2 tables")?;
        }
        Ok(())
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
        if !is_aligned_to_page_size(addr as u64) {
            bail!("addr {:#x} is not aligned to page size", addr as u64)
        }
        if !is_aligned_to_page_size(ipa.0) {
            bail!("ipa {:#x} is not aligned to page size", ipa.0)
        }
        if !is_aligned_to_page_size(size as u64) {
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
        let file = std::fs::File::open(filename)?;
        let map = unsafe { memmap::MmapOptions::default().map(&file) }
            .context("error mmmapping ELF file")?;
        let obj = object::read::File::parse(&map)?;
        use object::{Object, ObjectSection, ObjectSegment};

        struct SegmentState<'a, 'b> {
            segment: object::Segment<'a, 'b>,
            aligned_size: u64,
            flags: HvMemoryFlags,
            ipa: GuestIpaAddress,
            va: GuestVaAddress,
        }

        let mut segments = obj
            .segments()
            .scan(Offset(0), |mut_offset, segment| {
                let size = align_up_to_page_size(segment.size());
                let offset = *mut_offset;
                *mut_offset = mut_offset.add(Offset(size));
                let ipa = DRAM_IPA_START.add(offset);
                let va = GuestVaAddress(align_down_to_page_size(segment.address()));
                Some(SegmentState {
                    segment,
                    aligned_size: size,
                    ipa,
                    va,
                    flags: HvMemoryFlags::HV_MEMORY_READ,
                })
            })
            .collect::<Vec<_>>();

        for section in obj.sections() {
            if let Ok(segment_idx) = segments.binary_search_by(|seg| {
                use std::cmp::Ordering as O;
                if section.address() < seg.segment.address() {
                    return O::Greater;
                }
                if section.address() > seg.segment.address() + seg.segment.size() {
                    return O::Less;
                }
                O::Equal
            }) {
                let s = &mut segments[segment_idx];
                use object::SectionKind::*;
                // There's no API to get segment flags in object, at least I did not find it,
                // so just figure it out by the sectons we care about.
                match section.kind() {
                    Text => s.flags |= HvMemoryFlags::HV_MEMORY_EXEC,
                    Data | UninitializedData => s.flags |= HvMemoryFlags::HV_MEMORY_WRITE,
                    _ => {}
                };
            }
        }

        for (idx, ss) in segments.iter().enumerate() {
            macro_rules! _tt_msg {
                () => {
                    format_args!(
                        "configuring translation tables for LOAD segment {}, address {:#x?}, size {}, aligned size {}, IPA {:#x?}, VA {:#x?}, flags: {:?}",
                        idx,
                        ss.segment.address(),
                        ss.segment.size(),
                        ss.aligned_size,
                        ss.ipa.0,
                        ss.va.0,
                        ss.flags,
                    );
                }
            }
            debug!("{}", _tt_msg!());
            self.memory_manager
                .configure_page_tables(ss.ipa, ss.va, ss.aligned_size as usize, ss.flags)
                .with_context(|| anyhow!("error {}", _tt_msg!()))?;
        }

        for section in obj.sections() {
            let section_name = section.name().with_context(|| {
                format!(
                    "error determining section name at {:#x?}",
                    section.address()
                )
            })?;
            if let Ok(segment_idx) = segments.binary_search_by(|seg| {
                use std::cmp::Ordering as O;
                if section.address() < seg.segment.address() {
                    return O::Greater;
                }
                if section.address() > seg.segment.address() + seg.segment.size() {
                    return O::Less;
                }
                O::Equal
            }) {
                use object::SectionKind::*;
                match section.kind() {
                    Text | Data | UninitializedData | ReadOnlyData => {}
                    _ => continue,
                };
                let data = section.data().with_context(|| {
                    format!("error getting section data for section {}", section_name)
                })?;
                // let ipa = self.mem(section.address() - segment.va.0));

                let ipa = self
                    .memory_manager
                    .simulate_address_lookup(GuestVaAddress(section.address()))?
                    .unwrap();
                if !data.is_empty() {
                    debug!(
                        "loading section {} (segment {}), size {} into memory at {:#x?}, ipa {:#x?}",
                        section_name,
                        segment_idx,
                        section.size(),
                        section.address(),
                        ipa.0,
                    );
                    let slice = self
                        .memory_manager
                        .memory
                        .get_slice(ipa.as_guest_address(), section.size() as usize)
                        .with_context(|| {
                            format!(
                                "error getting the slice of memory for section {}",
                                section_name
                            )
                        })?;
                    slice.copy_from(data);
                }
            } else {
                trace!("ignoring section {}", section_name);
            }
        }
        let entrypoint = GuestVaAddress(obj.entry());
        debug!("entrypoint is {:#x?}", entrypoint.0);
        self.entrypoint = Some(entrypoint);

        // TODO: assumes the exception table is the first piece.
        // if let object::SectionKind::Text = section.kind() {
        //     self.vbar_el1 = Some(GuestVaAddress(section.address()));
        // };

        // TODO: remove this hardcode
        self.vbar_el1 = Some(GuestVaAddress(0x4000));

        Ok(LoadedElf { entrypoint })
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
    guest_pc: GuestVaAddress,
    guest_vbar_el1: GuestVaAddress,
    ttbr0: GuestIpaAddress,
    ttbr1: GuestIpaAddress,
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

    fn dfsc_desc(&self) -> &'static str {
        match self.dfsc() {
            0b000000 => {
                "Address size fault, level 0 of translation or translation table base register."
            }
            0b000001 => "Address size fault, level 1",
            0b000010 => "Address size fault, level 2",
            0b000011 => "Address size fault, level 3",
            0b000100 => "Translation fault, level 0",
            0b000101 => "Translation fault, level 1",
            0b000110 => "Translation fault, level 2",
            0b000111 => "Translation fault, level 3",
            0b001001 => "Access flag fault, level 1",
            0b001010 => "Access flag fault, level 2",
            0b001011 => "Access flag fault, level 3",
            0b001000 => "Access flag fault, level 0",
            0b001100 => "Permission fault, level 0",
            0b001101 => "Permission fault, level 1",
            0b001110 => "Permission fault, level 2",
            0b001111 => "Permission fault, level 3",
            _ => "unknown",
        }
    }
}

impl core::fmt::Debug for DataAbortFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ds = f.debug_struct("DataAbortFlags");

        ds.field("ISV (is_valid)", &self.is_valid());
        if let (Some(sas), Some(length), Some(sse), Some(srt), Some(sf), Some(af)) = (
            self.sas(),
            self.sas_len(),
            self.sse(),
            self.srt(),
            self.sf(),
            self.af(),
        ) {
            ds.field("sas", &sas)
                .field("sas_length()", &length)
                .field("sse", &sse)
                .field("srt", &srt)
                .field("register()", &format_args!("X{}", srt))
                .field("sf", &sf)
                .field("af", &af);
        };
        if self.dfsc() == 0b010000 {
            ds.field("far_is_valid", &self.far_is_valid());
        };

        ds.field("is_write", &self.is_write())
            .field("dfsc", &format_args!("{:#b}", self.dfsc()))
            .field("dfsc_description()", &self.dfsc_desc())
            .finish()
    }
}

#[repr(C)]
struct StartParams {
    dram_start: GuestVaAddress,
    dram_usable_start: GuestVaAddress,
    dram_size: u64,
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

        loop {
            assert_hv_return_t_ok(unsafe { bindgen::hv_vcpu_run(self.id) }, "hv_vcpu_run")?;

            let exit_t = self.exit_t();
            if exit_t.reason != HvExitReason::HV_EXIT_REASON_EXCEPTION {
                self.dump_all_registers()?;
                panic!("unexpected exit reason {:?}", exit_t.reason);
            }

            match exit_t.reason {
                HvExitReason::HV_EXIT_REASON_EXCEPTION => {}
                other => bail!("unsupported HvExitReason {:?}", other),
            };

            assert_eq!(exit_t.reason, HvExitReason::HV_EXIT_REASON_EXCEPTION);
            match exit_t.decoded_syndrome.exception_class {
                EXC_HVC => {
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
                            self.dump_all_registers()?;
                            return Ok(());
                        }
                        PANIC => {
                            self.dump_all_registers()?;
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
                                self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ESR_EL1)?,
                            );

                            match el1_syndrome.exception_class {
                                EXC_DATA_ABORT_SAME => {
                                    self.debug_data_abort(el1_syndrome.iss)?;
                                    name = "data abort";
                                }
                                EXC_SOFT_STEP_SAME | EXC_BREAKPOINT_SAME => {
                                    let instruction_address =
                                        self.get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_ELR_EL1)?;
                                    trace!(
                                        "Debug exception, address {:#x?}, continuing",
                                        instruction_address
                                    );
                                    let spsr_el1 = self
                                        .get_sys_reg(bindgen::hv_sys_reg_t_HV_SYS_REG_SPSR_EL1)?;
                                    // Set pstate.SS to 1, so that it actually executes the next instruction.
                                    self.set_sys_reg(
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
                            self.dump_all_registers()?;
                            self.print_stack()?;
                            bail!("HVC EL1 -> EL1 exception: {}", name);
                        }
                        PRINT_STRING => {
                            let addr = self.get_reg(bindgen::hv_reg_t_HV_REG_X0)?;
                            let len = self.get_reg(bindgen::hv_reg_t_HV_REG_X1)?;

                            let slice = unsafe {
                                self.memory_manager
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
                EXC_INSTR_ABORT_LOWER => {
                    error!("instruction abort");
                    self.dump_all_registers()?;
                    self.print_stack()?;
                    error!("{:#x?}", self.exit_t());
                    bail!("instruction abort");
                }
                EXC_DATA_ABORT_LOWER => {
                    self.debug_data_abort(self.exit_t().decoded_syndrome.iss)?;
                    bail!("data abort EL1 -> EL2");
                }
                _ => {
                    bail!(
                        "unsupported exception class {:#x?}",
                        exit_t.decoded_syndrome
                    )
                }
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
            assert_hv_return_t_ok(
                unsafe { bindgen::hv_vcpu_set_trap_debug_exceptions(self.id, true) },
                "hv_vcpu_set_trap_debug_exceptions",
            )?;
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

pub struct Syndrome {
    exception_class: u8,
    iss: u32,
    iss2: u8,
    il_32_bit: bool,
    original_value: u64,
}

const EXC_HVC: u8 = 0b010110;
const EXC_INSTR_ABORT_LOWER: u8 = 0b100000;
const EXC_INSTR_ABORT_SAME: u8 = 0b100001;
const EXC_DATA_ABORT_LOWER: u8 = 0b100100;
const EXC_DATA_ABORT_SAME: u8 = 0b100101;
const EXC_BREAKPOINT_SAME: u8 = 0b110001;
const EXC_BREAKPOINT_LOWER: u8 = 0b110000;
const EXC_SOFT_STEP_SAME: u8 = 0b110011;
const EXC_SOFT_STEP_LOWER: u8 = 0b110010;

struct InstructionAbortFlags(u32);
impl core::fmt::Debug for InstructionAbortFlags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ds = f.debug_struct("InstructionAbortFlags");

        let ifsc = self.0 & 0b111111;
        ds.field("ifsc (status code)", &ifsc);
        let ifsc_desc = match ifsc {
            0b000000 => {
                "Address size fault, level 0 of translation or translation table base register"
            }
            0b000001 => "Address size fault, level 1",
            0b000010 => "Address size fault, level 2",
            0b000011 => "Address size fault, level 3",
            0b000100 => "Translation fault, level 0",
            0b000101 => "Translation fault, level 1",
            0b000110 => "Translation fault, level 2",
            0b000111 => "Translation fault, level 3",
            0b001011 => "Access flag fault, level 3",
            0b001101 => "Permission fault, level 1",
            0b001110 => "Permission fault, level 2",
            0b001111 => "Permission fault, level 3",
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
            EXC_HVC => "HVC",
            EXC_INSTR_ABORT_LOWER => "Instruction abort (MMU) from lower EL",
            EXC_INSTR_ABORT_SAME => "Instruction abort (MMU) fault from same EL",
            EXC_DATA_ABORT_LOWER => "Data abort from a lower exception level",
            EXC_DATA_ABORT_SAME => "Data abort from the same exception level",
            EXC_SOFT_STEP_SAME => {
                "Software Step exception taken without a change in Exception level"
            }
            EXC_SOFT_STEP_LOWER => "Software Step exception from a lower Exception level",
            EXC_BREAKPOINT_LOWER => "Breakpoint exception from a lower Exception level",
            EXC_BREAKPOINT_SAME => "Breakpoint exception taken without a change in Exception level",
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
            EXC_INSTR_ABORT_SAME | EXC_INSTR_ABORT_LOWER => Some(InstructionAbortFlags(self.iss)),
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
