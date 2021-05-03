use std::{alloc::Layout, path::Path};

use crate::{
    addresses::GuestIpaAddress,
    error::{Error, Kind},
    GuestVaAddress, HvMemoryFlags, Offset,
};
use log::{debug, error, trace};

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: GuestVaAddress,
    pub vbar_el1: GuestVaAddress,
    pub used_dram_size: u64,
}
pub trait MemoryManager {
    fn aligner(&self) -> crate::aligner::Aligner;
    fn allocate_va(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> crate::Result<GuestVaAddress>;
    fn allocate_ipa(
        &mut self,
        layout: Layout,
        purpose: core::fmt::Arguments<'_>,
    ) -> crate::Result<(*mut u8, GuestIpaAddress)>;
    fn simulate_address_lookup(&self, va: GuestVaAddress)
        -> crate::Result<Option<GuestIpaAddress>>;
    fn configure_page_tables(
        &mut self,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
        size: usize,
        flags: HvMemoryFlags,
    ) -> crate::Result<()>;
    fn get_memory_slice(&mut self, va: GuestVaAddress, size: usize) -> crate::Result<&mut [u8]>;
}

pub fn load_elf<MM: MemoryManager, P: AsRef<Path>>(
    mm: &mut MM,
    filename: P,
) -> crate::Result<LoadedElf> {
    let file = std::fs::File::open(filename).map_err(Kind::FileOpen)?;
    let map = match unsafe { memmap::MmapOptions::default().map(&file) } {
        Ok(map) => map,
        Err(e) => return Err(Kind::MmapElfFile(e).into()),
    };
    let obj = object::read::File::parse(&map)?;
    use object::{Object, ObjectSection, ObjectSegment};

    struct SegmentState<'a, 'b> {
        segment: object::Segment<'a, 'b>,
        aligned_start: u64,
        aligned_size: u64,
        flags: HvMemoryFlags,
        ipa: GuestIpaAddress,
        va: GuestVaAddress,
    }

    let mut segments = Vec::new();

    let va_offset = mm.allocate_va(
        Layout::from_size_align(0, mm.aligner().align_up(1) as usize)?,
        format_args!("kernel loading"),
    )?;

    for (idx, segment) in obj.segments().enumerate() {
        let start = segment.address();
        let end = segment.address() + segment.size();
        let aligned_start = mm.aligner().align_down(start);
        let aligned_end = mm.aligner().align_up(end);
        let aligned_size = aligned_end - aligned_start;

        trace!("segment {}, start={:#x?}, end={:#x?}, size={}, aligned_start={:#x?}, aligned_end={:#x?}, aligned_size={}",
            idx, start, end, segment.size(), aligned_start, aligned_end, aligned_size
        );

        let layout = Layout::from_size_align(aligned_size as usize, segment.align() as usize)?;
        let va = va_offset.add(Offset(aligned_start));
        let (_, ipa) = mm.allocate_ipa(layout, format_args!("LOAD segment {}", idx))?;
        // let va = mm.allocate_va(layout, format_args!("LOAD segment {}", idx))?;
        // dbg!(mm.consume_va(aligned_size as usize));

        let ss = SegmentState {
            segment,
            aligned_size,
            aligned_start,
            ipa,
            va,
            flags: HvMemoryFlags::HV_MEMORY_READ,
        };
        segments.push(ss)
    }

    if let Some(last) = segments.last() {
        // Consume all the virtual address space needed for this binary.
        // Not all of it will be mapped later, just the required portions, but if the ELF is wasteful, so
        // will be the VA space.
        mm.allocate_va(
            Layout::from_size_align(
                (last.va.0 - va_offset.0 + last.aligned_size) as usize,
                mm.aligner().align_up(1) as usize,
            )?,
            format_args!("virtual address space for the binary"),
        )?;
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
        debug!(
            "configuring translation tables for LOAD segment {}, address {:#x?}, size {}, aligned size {}, IPA {:#x?}, VA {:#x?}, flags: {:?}",
            idx,
            ss.segment.address(),
            ss.segment.size(),
            ss.aligned_size,
            ss.ipa.0,
            ss.va.0,
            ss.flags,
        );
        mm.configure_page_tables(ss.ipa, ss.va, ss.aligned_size as usize, ss.flags)
            .map_err(|e| {
                let context_kind = Kind::TranslationForLoadSegment {
                    idx,
                    segment_address: ss.segment.address(),
                };
                e.push_kind(context_kind)
            })?
    }

    for section in obj.sections() {
        let section_name = section.name().map_err(|e| {
            let e = crate::error::Error::from(e);
            let kind = Kind::ErrorReadingSectionName {
                address: section.address(),
            };
            e.push_kind(kind)
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
            let data = section.data().map_err(|e| {
                error!("error getting section data for section {}", section_name);
                let e = crate::error::Error::from(e);
                e.push_kind(Kind::ErrorReadingSectionData {
                    section_address: section.address(),
                })
            })?;

            let va = {
                let segment_state = &segments[segment_idx];
                let offset = Offset(section.address() - segment_state.aligned_start);
                segment_state.va.add(offset)
            };

            let ipa = mm.simulate_address_lookup(va)?.ok_or_else(|| {
                Kind::ElfLoaderCannotSimulateAddressLookupInSection {
                    va,
                    section_address: section.address(),
                    segment_idx,
                }
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
                let slice = mm.get_memory_slice(va, section.size() as usize)?;
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
    let vbar_el1 = vbar_el1.ok_or(Kind::NoExceptionVectorTable)?;

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
                    let mut relocation_mem = mm
                        .get_memory_slice(va, core::mem::size_of::<u64>())
                        .map_err(|e| {
                        error!("error getting memory for {:?}: {}", &d, &e);
                        e
                    })?;
                    let relocation_value = if reloc.addend() >= 0 {
                        va_offset.add(Offset(reloc.addend() as u64))
                    } else {
                        error!("relocation addend negative, not supported: {:?}", &d);
                        return Err(Error::string("relocation addend negative, not supported"));
                    };
                    use byteorder::WriteBytesExt;

                    relocation_mem
                        .write_u64::<byteorder::LittleEndian>(relocation_value.0)
                        .map_err(|e| {
                            error!(
                                "error writing value {:#x?} at VA {:#x?} for {:?}",
                                relocation_value.0, va.0, &d
                            );
                            Kind::ByteOrderWriteError(e)
                        })?;
                    trace!(
                        "wrote value {:#x?} at VA {:#x?} for {:?}",
                        relocation_value.0,
                        va.0,
                        &d
                    );
                }
                _ => {
                    error!("unsupported relocation offset {:#x?}, {:?}", offset, reloc);
                    return Err(Error::string("relocation configuration unsupported"));
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
