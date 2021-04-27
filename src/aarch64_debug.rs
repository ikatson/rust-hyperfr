pub struct Syndrome {
    pub exception_class: u8,
    pub iss: u32,
    pub iss2: u8,
    pub il_32_bit: bool,
    pub original_value: u64,
}

pub const EXC_HVC: u8 = 0b010110;
pub const EXC_INSTR_ABORT_LOWER: u8 = 0b100000;
pub const EXC_INSTR_ABORT_SAME: u8 = 0b100001;
pub const EXC_DATA_ABORT_LOWER: u8 = 0b100100;
pub const EXC_DATA_ABORT_SAME: u8 = 0b100101;
pub const EXC_BREAKPOINT_SAME: u8 = 0b110001;
pub const EXC_BREAKPOINT_LOWER: u8 = 0b110000;
pub const EXC_SOFT_STEP_SAME: u8 = 0b110011;
pub const EXC_SOFT_STEP_LOWER: u8 = 0b110010;

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

pub struct DataAbortFlags(pub u32);

impl DataAbortFlags {
    pub fn is_valid(&self) -> bool {
        ((self.0 >> 24) & 1) == 1
    }
    pub fn sas(&self) -> Option<u8> {
        if self.is_valid() {
            Some(((self.0 >> 22) & 0b11) as u8)
        } else {
            None
        }
    }
    pub fn sas_len(&self) -> Option<u8> {
        self.sas().map(|sas| 1 << sas)
    }
    pub fn sse(&self) -> Option<bool> {
        if self.is_valid() {
            Some(((self.0 >> 21) & 1) == 1)
        } else {
            None
        }
    }
    pub fn srt(&self) -> Option<u8> {
        if self.is_valid() {
            Some(((self.0 >> 16) & 31) as u8)
        } else {
            None
        }
    }
    pub fn sf(&self) -> Option<bool> {
        if self.is_valid() {
            Some(((self.0 >> 15) & 1) == 1)
        } else {
            None
        }
    }
    pub fn af(&self) -> Option<bool> {
        if self.is_valid() {
            Some(((self.0 >> 15) & 1) == 1)
        } else {
            None
        }
    }

    pub fn is_write(&self) -> bool {
        ((self.0 >> 6) & 1) == 1
    }

    pub fn far_is_valid(&self) -> bool {
        ((self.0 >> 10) & 1) == 0
    }

    pub fn dfsc(&self) -> u8 {
        (self.0 & 0b11111) as u8
    }

    pub fn dfsc_desc(&self) -> &'static str {
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
