use vm_memory::GuestAddress;

#[derive(Copy, Clone)]
pub struct GuestIpaAddress(pub u64);
impl GuestIpaAddress {
    pub const fn add(&self, offset: Offset) -> GuestIpaAddress {
        GuestIpaAddress(self.0 + offset.0)
    }
    pub const fn as_guest_address(&self) -> GuestAddress {
        GuestAddress(self.0)
    }
}

impl core::fmt::Debug for GuestIpaAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("IPA({:#x?})", self.0))
    }
}

#[derive(Copy, Clone, Default)]
pub struct GuestVaAddress(pub u64);
impl GuestVaAddress {
    pub const fn add(&self, offset: Offset) -> GuestVaAddress {
        GuestVaAddress(self.0 + offset.0)
    }

    pub fn checked_sub(&self, offset: Offset) -> Option<GuestVaAddress> {
        self.0.checked_sub(offset.0).map(GuestVaAddress)
    }
}

impl core::fmt::Debug for GuestVaAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("VA({:#x?})", self.0))
    }
}

#[derive(Copy, Clone)]
pub struct Offset(pub u64);
impl Offset {
    pub const fn add(&self, offset: Offset) -> Offset {
        Offset(self.0 + offset.0)
    }
}

impl core::fmt::Debug for Offset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("Offset({:#x?})", self.0))
    }
}

#[derive(Debug)]
pub struct VaIpa {
    pub va: GuestVaAddress,
    pub ipa: GuestIpaAddress,
}
