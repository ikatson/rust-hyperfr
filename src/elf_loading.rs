use std::path::Path;

use crate::addresses::Offset;
use crate::layout::{DRAM_IPA_START, DRAM_VA_START};
use crate::GuestIpaAddress;
use crate::HvMemoryFlags;
use crate::{addresses::GuestVaAddress, HfVmBuilder};
use anyhow::{anyhow, bail, Context};
use log::{debug, trace};

use vm_memory::GuestMemory;

#[derive(Default)]
pub struct LoadedElf {
    pub entrypoint: GuestVaAddress,
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

impl HfVmBuilder {
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

        let va_offset = DRAM_VA_START;

        let mut segments = obj
            .segments()
            .scan(Offset(0), |mut_offset, segment| {
                let start = segment.address();
                let end = segment.address() + segment.size();
                let aligned_start = crate::aligner::ALIGNER_16K.align_down(start);
                let aligned_end = crate::aligner::ALIGNER_16K.align_up(end);
                let aligned_size = aligned_end - aligned_start;

                let offset = *mut_offset;
                *mut_offset = mut_offset.add(Offset(aligned_size));
                let ipa = DRAM_IPA_START.add(offset);
                let va = va_offset.add(Offset(aligned_start));
                Some(SegmentState {
                    segment,
                    aligned_size,
                    ipa,
                    va,
                    flags: HvMemoryFlags::HV_MEMORY_READ,
                })
            })
            .collect::<Vec<_>>();

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

                let ipa = self.memory_manager.simulate_address_lookup(va)?.unwrap();
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
                    let slice = self
                        .memory_manager
                        .memory
                        .get_slice(ipa.as_guest_address(), section.size() as usize)
                        .with_context(|| {
                            format!(
                                "error getting the slice of memory for section \"{}\"",
                                section_name
                            )
                        })?;
                    slice.copy_from(data);
                }
            } else {
                trace!("ignoring section {}", section_name);
            }
        }
        let entrypoint = va_offset.add(Offset(obj.entry()));
        debug!("entrypoint is {:#x?}", entrypoint.0);
        self.entrypoint = Some(entrypoint);

        use object::ObjectSymbol;
        for symbol in obj.symbols() {
            if symbol.name().unwrap_or_default() == "exception_vector_table" {
                self.vbar_el1 = Some(va_offset.add(Offset(symbol.address())));
            }
        }

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
                        let mut relocation_mem = unsafe {
                            self.memory_manager
                                .get_memory_slice(va, core::mem::size_of::<u64>())
                                .with_context(|| format!("error getting memory for {:?}", &d))?
                        };
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

        Ok(LoadedElf { entrypoint })
    }
}
