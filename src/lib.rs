use std::marker::PhantomData;

use private::Sealed;

mod private {
    pub trait Sealed {}
}

impl private::Sealed for u8 {}
impl private::Sealed for u16 {}
impl private::Sealed for u32 {}
impl private::Sealed for u64 {}

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

/// defines the maximum bit offset for a type which
/// can be read as a series of bits.
/// this trait can not be implemented by any other type.
pub trait Bits: Sized + private::Sealed {
    /// max. offset from the least significant bit
    const MAX_BIT_OFFSET: usize;
    const MAX_MASK: Self;
}

macro_rules! impl_bits {
    ($t:ty,$o:expr) => {
        impl Bits for $t {
            const MAX_BIT_OFFSET: usize = $o;
            const MAX_MASK: $t = Self::MAX;
        }
    };
}

impl_bits!(u8, 7);
impl_bits!(u16, 15);
impl_bits!(u32, 31);
impl_bits!(u64, 63);

#[derive(Debug)]
pub enum BytersError {
    BitPositionBound { given: usize, max: usize },
    BitRangeInvalid { start: usize, end: usize },
}

/// generic `Result` type for the `byters` crate
pub type BytersResult<T> = Result<T, BytersError>;

/// the position of a bit in a type T which implements
/// the `HiBit` trait.
/// Ensures position validity on initialization.
pub struct BitPos<T: Bits> {
    pub(crate) pos: usize,
    phantomdata: PhantomData<T>,
}

impl<T> BitPos<T>
where
    T: Bits,
{
    /// validates that the given bit offset `p` is inside
    /// the bounds of the bits of Type `T`.
    /// Returns a `BitPositionBound` error if the passed
    /// `p` exceeds the max. bit offset for Type `T`.
    pub fn new(p: usize) -> BytersResult<BitPos<T>> {
        if p > T::MAX_BIT_OFFSET {
            return Err(BytersError::BitPositionBound {
                given: p,
                max: T::MAX_BIT_OFFSET,
            });
        }
        return Ok(Self {
            pos: p,
            phantomdata: PhantomData,
        });
    }
}

pub struct BitRange<T: Bits> {
    pub(crate) start: usize,
    pub(crate) end: usize,
    phantomdata: PhantomData<T>,
}

impl<T> BitRange<T>
where
    T: Bits,
{
    pub fn new(start: usize, end: usize) -> BytersResult<BitRange<T>> {
        if start >= end {
            return Err(BytersError::BitRangeInvalid { start, end });
        }
        if end > T::MAX_BIT_OFFSET {
            return Err(BytersError::BitPositionBound {
                given: end,
                max: T::MAX_BIT_OFFSET,
            });
        }
        Ok(BitRange {
            start,
            end,
            phantomdata: PhantomData,
        })
    }

    pub(crate) fn mask_lshift(&self) -> usize {
        T::MAX_BIT_OFFSET - self.end
    }

    pub(crate) fn mask_rshift(&self) -> usize {
        self.mask_lshift() + self.start
    }
}

/// a type which implement `Bits` can read a bit
/// at position `pos`.
/// the validity of the position is enforced on the type level
pub trait ReadableBit: Bits {
    fn read_bit(&self, pos: BitPos<Self>) -> u8;
}

macro_rules! impl_readable_bit {
    ($s:ty) => {
        impl ReadableBit for $s {
            fn read_bit(&self, pos: BitPos<$s>) -> u8 {
                ((self >> pos.pos) & 1) as u8
            }
        }
    };
}

impl_readable_bit!(u8);
impl_readable_bit!(u16);
impl_readable_bit!(u32);
impl_readable_bit!(u64);

pub trait SetableBit: Bits {
    fn set_bit(&mut self, pos: BitPos<Self>);
}

macro_rules! impl_setable_bit {
    ($s:ty) => {
        impl SetableBit for $s {
            fn set_bit(&mut self, pos: BitPos<$s>) {
                *self |= (1 << pos.pos);
            }
        }
    };
}

impl_setable_bit!(u8);
impl_setable_bit!(u16);
impl_setable_bit!(u32);
impl_setable_bit!(u64);

pub trait SetableBits: Bits {
    fn set_bits(&mut self, range: BitRange<Self>);
}

macro_rules! impl_setable_bits {
    ($s:ty) => {
        impl SetableBits for $s {
            fn set_bits(&mut self, range: BitRange<$s>) {
                let mask =
                    ((<$s>::MAX_MASK << range.mask_lshift()) >> range.mask_rshift()) << range.start;
                *self |= mask;
            }
        }
    };
}

impl_setable_bits!(u8);
impl_setable_bits!(u16);

/// read a range of bits starting from bit index `start` up to and including
/// `end` returning it as a `T`.
/// `start` and `end` are treated as 0-based indices
pub trait BitsReadableAs<T>: Bits {
    fn read_bits_as(&self, range: BitRange<Self>) -> T;
}

macro_rules! impl_bits_readable_as {
    ($s:ty,$o:ty) => {
        impl BitsReadableAs<$o> for $s {
            fn read_bits_as(&self, range: BitRange<$s>) -> $o {
                ((self << range.mask_lshift()) >> range.mask_rshift()) as $o
            }
        }
    };
}

impl_bits_readable_as!(u8, u8);
impl_bits_readable_as!(u8, u16);
impl_bits_readable_as!(u16, u8);

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

/// read primitiv number type into byte array with BE ordering
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

/// read primitiv number type into byte array with LE ordering
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
    use crate::{
        BigEndian, BitPos, BitRange, BitsReadableAs, LittleEndian, ReadableBit, ReadsFromBytes,
        ReadsIntoBytes, SetableBit, SetableBits,
    };

    #[test]
    fn bits_readable() {
        let val_u8: u8 = 0b1010_1010;
        let r = BitRange::<u8>::new(1, 5).unwrap();
        let out: u8 = val_u8.read_bits_as(r);
        assert_eq!(out, 0b0010101);
    }

    #[test]
    fn bit_readable() {
        let val_u8: u8 = 0b0001_0000;
        let pos_4_u8 = BitPos::<u8>::new(4).unwrap();
        let pos_3_u8 = BitPos::<u8>::new(3).unwrap();
        assert_eq!(val_u8.read_bit(pos_4_u8), 1);
        assert_eq!(val_u8.read_bit(pos_3_u8), 0);
        let pos_8_u16 = BitPos::<u16>::new(8).unwrap();
        let val_u16: u16 = 0x0100;
        assert_eq!(val_u16.read_bit(pos_8_u16), 1);
        let pos_16_u32 = BitPos::<u32>::new(16).unwrap();
        let val_u32: u32 = 0x00010000;
        assert_eq!(val_u32.read_bit(pos_16_u32), 1);
    }

    #[test]
    fn read_from_bytes_le() {
        let val_u16: [u8; 2] = [0xAA, 0xBB];
        assert_eq!(LittleEndian::read_into_u16(val_u16), 0xBBAA);
        let val_u32: [u8; 4] = [0xAA, 0xBB, 0xCC, 0xDD];
        assert_eq!(LittleEndian::read_into_u32(val_u32), 0xDDCCBBAA);
        let val_u64: [u8; 8] = [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        assert_eq!(LittleEndian::read_into_u64(val_u64), 0x7766554433221100);
    }

    #[test]
    fn read_into_bytes_le() {
        let val_u16: u16 = 0xAABB;
        assert_eq!(LittleEndian::read_from_u16(val_u16), [0xBB, 0xAA]);
        let val_u32: u32 = 0xAABBCCDD;
        assert_eq!(
            LittleEndian::read_from_u32(val_u32),
            [0xDD, 0xCC, 0xBB, 0xAA]
        );
    }

    #[test]
    fn read_from_bytes_be() {
        let val_u16: [u8; 2] = [0xAA, 0xBB];
        assert_eq!(BigEndian::read_into_u16(val_u16), 0xAABB);
        let val_u32: [u8; 4] = [0xAA, 0xBB, 0xCC, 0xDD];
        assert_eq!(BigEndian::read_into_u32(val_u32), 0xAABBCCDD);
    }

    #[test]
    fn read_into_bytes_be() {
        let val_u16: u16 = 0xAABB;
        assert_eq!(BigEndian::read_from_u16(val_u16), [0xAA, 0xBB]);
        let val_u32: u32 = 0xAABBCCDD;
        assert_eq!(BigEndian::read_from_u32(val_u32), [0xAA, 0xBB, 0xCC, 0xDD]);
        let val_u64: u64 = 0x0011223344556677;
        assert_eq!(
            BigEndian::read_from_u64(val_u64),
            [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77]
        )
    }

    #[test]
    fn set_bit() {
        let pos_2_u8 = BitPos::<u8>::new(2).unwrap();
        let mut val_u8: u8 = 0;
        val_u8.set_bit(pos_2_u8);
        assert_eq!(val_u8, 4);
    }

    #[test]
    fn set_bits() {
        let mut val_u8 = 0u8;
        let r = BitRange::<u8>::new(1, 3).unwrap();
        val_u8.set_bits(r);
        assert_eq!(val_u8, 14);
    }
}
