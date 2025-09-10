use private::Sealed;

mod private {
    pub trait Sealed {}
}

impl private::Sealed for u8 {}
impl private::Sealed for u16 {}

pub type Nibble = u8;

pub trait Byte: private::Sealed {
    fn hi_nibble(&self) -> Nibble;
    fn lo_nibble(&self) -> Nibble;
}

impl Byte for u8 {
    fn hi_nibble(&self) -> Nibble {
        (self & 0xF0) >> 4
    }
    fn lo_nibble(&self) -> Nibble {
        self & 0x0F
    }
}

/// read the bit at `pos` as a single byte
/// positions are treated as 0-based indices,
/// treating the least significant bit as the
/// first index
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

/// defines the highest bit index for a type.
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

/// unified API for reading data in big endian
/// order
pub struct BigEndian {}

impl Sealed for BigEndian {}

/// unified API for reading data in little endian
/// order
pub struct LittleEndian {}

impl Sealed for LittleEndian {}

/// wrapper trait for reading bytes as primitiv number types
pub trait ReadsFromBytes: private::Sealed {
    fn read_into_u16(bytes: [u8; 2]) -> u16;
    fn read_into_u32(bytes: [u8; 4]) -> u32;
    fn read_into_u64(bytes: [u8; 8]) -> u64;
}

impl ReadsFromBytes for BigEndian {
    fn read_into_u16(bytes: [u8; 2]) -> u16 {
        u16::from_be_bytes(bytes)
    }

    fn read_into_u32(bytes: [u8; 4]) -> u32 {
        u32::from_be_bytes(bytes)
    }

    fn read_into_u64(bytes: [u8; 8]) -> u64 {
        u64::from_be_bytes(bytes)
    }
}

impl ReadsFromBytes for LittleEndian {
    fn read_into_u16(bytes: [u8; 2]) -> u16 {
        u16::from_le_bytes(bytes)
    }

    fn read_into_u32(bytes: [u8; 4]) -> u32 {
        u32::from_le_bytes(bytes)
    }

    fn read_into_u64(bytes: [u8; 8]) -> u64 {
        u64::from_le_bytes(bytes)
    }
}

/// wrapper trait for reading primitiv number types into bytes
pub trait ReadsIntoBytes: private::Sealed {
    fn read_from_u16(n: u16) -> [u8; 2];
    fn read_from_u32(n: u32) -> [u8; 4];
    fn read_from_u64(n: u64) -> [u8; 8];
}

impl ReadsIntoBytes for BigEndian {
    fn read_from_u16(n: u16) -> [u8; 2] {
        n.to_be_bytes()
    }

    fn read_from_u32(n: u32) -> [u8; 4] {
        n.to_be_bytes()
    }

    fn read_from_u64(n: u64) -> [u8; 8] {
        n.to_be_bytes()
    }
}

impl ReadsIntoBytes for LittleEndian {
    fn read_from_u16(n: u16) -> [u8; 2] {
        n.to_le_bytes()
    }

    fn read_from_u32(n: u32) -> [u8; 4] {
        n.to_le_bytes()
    }

    fn read_from_u64(n: u64) -> [u8; 8] {
        n.to_le_bytes()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BitsReadableAs, LittleEndian, ReadableBit, ReadsFromBytes, ReadsIntoBytes};

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

    #[test]
    fn read_from_bytes_le() {
        let bytes_u16: [u8; 2] = [0xAA, 0xBB];
        assert_eq!(LittleEndian::read_into_u16(bytes_u16), 0xBBAA);
    }

    #[test]
    fn read_into_bytes_le() {
        let val_u16: u16 = 0xAABB;
        assert_eq!(LittleEndian::read_from_u16(val_u16), [0xBB, 0xAA]);
    }
}
