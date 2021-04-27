use vm_memory::GuestAddress;

#[derive(Copy, Clone, Debug)]
pub struct GuestIpaAddress(pub u64);
impl GuestIpaAddress {
    pub const fn add(&self, offset: Offset) -> GuestIpaAddress {
        GuestIpaAddress(self.0 + offset.0)
    }
    pub const fn as_guest_address(&self) -> GuestAddress {
        GuestAddress(self.0)
    }
}

#[derive(Copy, Clone, Default, Debug)]
pub struct GuestVaAddress(pub u64);
impl GuestVaAddress {
    pub const fn add(&self, offset: Offset) -> GuestVaAddress {
        GuestVaAddress(self.0 + offset.0)
    }

    pub fn checked_sub(&self, offset: Offset) -> Option<GuestVaAddress> {
        self.0.checked_sub(offset.0).map(GuestVaAddress)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Offset(pub u64);
impl Offset {
    pub const fn add(&self, offset: Offset) -> Offset {
        Offset(self.0 + offset.0)
    }
}

#[derive(Debug)]
pub struct VaIpa {
    pub va: GuestVaAddress,
    pub ipa: GuestIpaAddress,
}
