use std::{alloc::Layout, path::Path};

use crate::{addresses::GuestIpaAddress, GuestVaAddress, HvMemoryFlags, Offset};
use anyhow::{anyhow, bail, Context};
use log::{debug, trace};

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: GuestVaAddress,
    pub vbar_el1: GuestVaAddress,
    pub used_dram_size: u64,
}
pub trait MemoryManager {
    fn aligner(&self) -> crate::aligner::Aligner;
    fn get_binary_load_address(&mut self) -> GuestVaAddress;
    fn consume_va(&mut self, size: usize) -> GuestVaAddress;
    fn allocate_va(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> anyhow::Result<GuestVaAddress>;
    fn allocate_ipa(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> anyhow::Result<(*mut u8, GuestIpaAddress)>;
    fn simulate_address_lookup(
        &self,
        va: GuestVaAddress,
    ) -> anyhow::Result<Option<GuestIpaAddress>>;
    fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> anyhow::Result<()>;
    fn get_memory_slice(&mut self, va: GuestVaAddress, size: usize) -> anyhow::Result<&mut [u8]>;
}

pub fn load_elf<MM: MemoryManager, P: AsRef<Path>>(
    mm: &mut MM,
    filename: P,
) -> anyhow::Result<LoadedElf> {
    let file = std::fs::File::open(filename)?;
    let map =
        unsafe { memmap::MmapOptions::default().map(&file) }.context("error mmmapping ELF file")?;
    let obj = object::read::File::parse(&map)?;
    use object::{Object, ObjectSection, ObjectSegment};

    struct SegmentState<'a, 'b> {
        segment: object::Segment<'a, 'b>,
        aligned_size: u64,
        flags: HvMemoryFlags,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
    }

    let mut segments = Vec::new();

    let va_offset = mm.get_binary_load_address();

    for (idx, segment) in obj.segments().enumerate() {
        let start = segment.address();
        let end = segment.address() + segment.size();
        let aligned_start = mm.aligner().align_down(start);
        if idx == 0 {
            dbg!(mm.consume_va(aligned_start as usize));
        }
        let aligned_end = mm.aligner().align_up(end);
        let aligned_size = aligned_end - aligned_start;

        let layout = Layout::from_size_align(aligned_size as usize, segment.align() as usize)?;
        // let va = va_offset.add(Offset(aligned_start));
        let (_, ipa) = mm.allocate_ipa(layout, format_args!("LOAD segment {}", idx))?;
        let va = mm.allocate_va(layout, format_args!("LOAD segment {}", idx))?;
        // dbg!(mm.consume_va(aligned_size as usize));

        let ss = SegmentState {
            segment,
            aligned_size,
            ipa,
            va,
            flags: HvMemoryFlags::HV_MEMORY_READ,
        };
        segments.push(ss)
    }

    let used_dram_size = segments.iter().map(|s| s.aligned_size).sum();

    for section in obj.sections() {
        use object::SectionKind::*;
        match section.kind() {
            Text | Data | UninitializedData | ReadOnlyData => {}
            _ => continue,
        };
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
        mm.configure_page_tables(ss.ipa, ss.va, ss.aligned_size as usize, ss.flags)
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
                _ => {
                    debug!(
                        "ignoring section with name \"{}\", address {:#x?}, kind: {:?}",
                        section_name,
                        section.address(),
                        section.kind()
                    );
                    continue;
                }
            };
            let data = section.data().with_context(|| {
                format!("error getting section data for section {}", section_name)
            })?;

            let va = va_offset.add(Offset(section.address()));

            let ipa = mm.simulate_address_lookup(va)?.ok_or_else(|| {
                anyhow!(
                    "couldn't lookup address {:?} for section \"{}\", it should have been mapped together with segment {}",
                    va,
                    section_name,
                    segment_idx
                )
            })?;
            if !data.is_empty() {
                debug!(
                    "loading section \"{}\" (segment {}), size {}, kind {:?} into memory at {:#x?}, ipa {:#x?}",
                    section_name,
                    segment_idx,
                    section.size(),
                    section.kind(),
                    va.0,
                    ipa.0,
                );
                let slice = mm
                    .get_memory_slice(va, section.size() as usize)
                    .with_context(|| {
                        format!(
                            "error getting the slice of memory for section \"{}\" at {:?}",
                            section_name, va
                        )
                    })?;
                slice.copy_from_slice(data);
            }
        } else {
            trace!("ignoring section {}", section_name);
        }
    }
    let entrypoint = va_offset.add(Offset(obj.entry()));
    debug!("entrypoint is {:#x?}", entrypoint.0);

    use object::ObjectSymbol;
    let mut vbar_el1 = None;
    for symbol in obj.symbols() {
        if symbol.name().unwrap_or_default() == "exception_vector_table" {
            vbar_el1 = Some(va_offset.add(Offset(symbol.address())));
        }
    }
    let vbar_el1 =
        vbar_el1.ok_or_else(|| anyhow!("could not find symbol \"exception_vector_table\""))?;

    if let Some(relocs) = obj.dynamic_relocations() {
        for (offset, reloc) in relocs {
            const R_AARCH64_RELATIVE: u32 = 1027;

            match (reloc.kind(), reloc.target()) {
                (
                    object::RelocationKind::Elf(R_AARCH64_RELATIVE),
                    object::RelocationTarget::Absolute,
                ) => {
                    let d = RelocationDebugInfo {
                        offset,
                        rel: &reloc,
                    };
                    let va = va_offset.add(Offset(offset));
                    let mut relocation_mem =
                        mm.get_memory_slice(va, core::mem::size_of::<u64>())
                            .with_context(|| format!("error getting memory for {:?}", &d))?;
                    let relocation_value = if reloc.addend() >= 0 {
                        va_offset.add(Offset(reloc.addend() as u64))
                    } else {
                        bail!("relocation addend negative, not supported: {:?}", &d)
                    };
                    use byteorder::WriteBytesExt;

                    relocation_mem
                        .write_u64::<byteorder::LittleEndian>(relocation_value.0)
                        .with_context(|| {
                            format!(
                                "error writing value {:#x?} at VA {:#x?} for {:?}",
                                relocation_value.0, va.0, &d
                            )
                        })?;
                    trace!(
                        "wrote value {:#x?} at VA {:#x?} for {:?}",
                        relocation_value.0,
                        va.0,
                        &d
                    );
                }
                _ => {
                    bail!("unsupported relocation offset {:#x?}, {:?}", offset, reloc)
                }
            }
        }
    }

    Ok(LoadedElf {
        entrypoint,
        vbar_el1,
        used_dram_size,
    })
}

struct RelocationDebugInfo<'a> {
    offset: u64,
    rel: &'a object::Relocation,
}

impl<'a> core::fmt::Debug for RelocationDebugInfo<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Relocation")
            .field("offset", &format_args!("{:#x?}", self.offset))
            .field("addend", &format_args!("{:#x?}", self.rel.addend()))
            .finish()
    }
}
