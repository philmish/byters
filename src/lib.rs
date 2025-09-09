mod private {
    pub trait Sealed {}
}

pub type Nibble = u8;

pub trait Byte: private::Sealed {
    fn hi_nibble(&self) -> Nibble;
    fn lo_nibble(&self) -> Nibble;
}

impl private::Sealed for u8 {}
impl private::Sealed for u16 {}

impl Byte for u8 {
    fn hi_nibble(&self) -> Nibble {
        (self & 0xF0) >> 4
    }
    fn lo_nibble(&self) -> Nibble {
        self & 0x0F
    }
}

/// read the bit at `pos` as a single byte, positions are treated as 0-based indices
pub trait ReadableBit: HiBit + private::Sealed {
    fn read_bit(&self, pos: usize) -> u8;
}

macro_rules! impl_readable_bit {
    ($s:ty) => {
        impl ReadableBit for $s {
            fn read_bit(&self, pos: usize) -> u8 {
                let last_bit = Self::hi_bit_idx();
                assert!(last_bit >= pos);
                ((self >> pos) & 1) as u8
            }
        }
    };
}

impl_readable_bit!(u8);
impl_readable_bit!(u16);

/// read a range of bits starting from bit index `start` up to and including
/// `end` returning it as a `T`.
/// `start` and `end` are treated as 0-based indices
pub trait BitsReadableAs<T>: HiBit + private::Sealed {
    fn read_bits_as(&self, start: usize, end: usize) -> T;
}

macro_rules! impl_bits_readable_as {
    ($s:ty,$o:ty) => {
        impl BitsReadableAs<$o> for $s {
            fn read_bits_as(&self, start: usize, end: usize) -> $o {
                assert!(start < end);
                let hi_bit_idx = Self::hi_bit_idx();
                assert!(end <= hi_bit_idx);
                let r = hi_bit_idx - end;
                let l = r + start;
                ((self << r) >> l) as $o
            }
        }
    };
}

impl_bits_readable_as!(u8, u8);
impl_bits_readable_as!(u8, u16);
impl_bits_readable_as!(u16, u8);

pub trait HiBit {
    fn hi_bit_idx() -> usize;
}

macro_rules! impl_hi_bit {
    ($t:ty,$o:expr) => {
        impl HiBit for $t {
            fn hi_bit_idx() -> usize {
                $o
            }
        }
    };
}

impl_hi_bit!(u8, 7);
impl_hi_bit!(u16, 15);

#[cfg(test)]
mod tests {
    use crate::{BitsReadableAs, ReadableBit};

    #[test]
    fn bits_readable() {
        let val_u8: u8 = 0b1010_1010;
        let out: u8 = val_u8.read_bits_as(1, 5);
        assert_eq!(out, 0b0010101);
    }

    #[test]
    fn bit_readable() {
        let val_u8: u8 = 0b0001_0000;
        assert_eq!(val_u8.read_bit(4), 1);
        assert_eq!(val_u8.read_bit(3), 0);
    }
}
