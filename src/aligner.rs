use anyhow::bail;

pub const ALIGNER_16K: Aligner = Aligner::new_from_mask(!((1 << 14) - 1));

pub fn is_power_of_two(x: u64) -> bool {
    (x & (x - 1)) == 0 && x > 0
}

pub struct Aligner {
    mask: u64,
}

impl Aligner {
    pub const fn size(&self) -> u64 {
        !(self.mask) + 1
    }
    pub const fn new_from_mask(mask: u64) -> Self {
        Self { mask }
    }
    pub const fn is_aligned(&self, value: u64) -> bool {
        self.align_down(value) == value
    }
    pub const fn align_down(&self, value: u64) -> u64 {
        value & self.mask
    }
    pub const fn align_up(&self, value: u64) -> u64 {
        if !self.is_aligned(value) {
            self.align_down(value) + self.size()
        } else {
            value
        }
    }

    pub fn new_from_bits(bits: u8) -> anyhow::Result<Self> {
        match bits {
            1..=63 => Ok(Self {
                mask: !((1 << (bits - 1)) - 1),
            }),
            _ => bail!("bits should be >= 0 and =< 64"),
        }
    }
    pub fn new_from_power_of_two(number: u64) -> anyhow::Result<Self> {
        if !(is_power_of_two(number)) {
            bail!("{} is not a power of 2", number);
        }
        Ok(Self { mask: number - 1 })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pow_of_2() {
        for bits in 1u64..63 {
            assert!(
                is_power_of_two(1 << bits),
                "{} should be a power of 2",
                1 << bits
            );
            if bits > 1 {
                assert!(
                    !is_power_of_two((1 << bits) - 1),
                    "{} should not be a power of 2",
                    (1 << bits) - 1
                );
            }
        }
    }

    #[test]
    fn test_align_down_to_page_size() {
        assert_eq!(ALIGNER_16K.align_down(16385), 16384)
    }

    #[test]
    fn test_align_up_to_page_size() {
        assert_eq!(ALIGNER_16K.align_up(16385), 16384 * 2)
    }

    #[test]
    fn test_is_aligned_down_to_page_size() {
        assert_eq!(ALIGNER_16K.is_aligned(0x0000000101408000), true);
        assert_eq!(ALIGNER_16K.is_aligned(0x0000000103194000), true);
    }
}
