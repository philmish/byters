use std::marker::PhantomData;

use private::Sealed;

/// helper trait to seal implementation of internal
/// traits from outside sources
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

/// trait used as a base for reading and setting bits
/// all types which implement this trait treat positions
/// and ranges of bits as an offset from the least significant
/// bit.
/// the trait defines the maximum bit offset for a type which
/// can be read as a series of bits.
pub trait Bits: Sized + private::Sealed {
    /// max. offset from the least significant bit
    const MAX_BIT_OFFSET: usize;
    /// all bits in the implementing type set to `1`
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

/// offset into the bits of a type `T` which implements
/// the `Bits` trait, starting from the least significant bit.
/// enforces validity of the offset at creation of the
/// `BitOffset`.
#[derive(Clone, Copy)]
pub struct BitOffset<T: Bits> {
    pub(crate) pos: usize,
    phantomdata: PhantomData<T>,
}

/// implementation for `BitOffset` for every type implementing the
/// `Bits` trait.
impl<T> BitOffset<T>
where
    T: Bits,
{
    /// validates that the given bit offset `p` is inside
    /// the bounds of the bits of Type `T`.
    /// Returns a `BitPositionBound` error if the passed
    /// `p` exceeds the max. bit offset for Type `T`.
    pub fn new(p: usize) -> BytersResult<BitOffset<T>> {
        if p > T::MAX_BIT_OFFSET {
            return Err(BytersError::BitPositionBound {
                given: p,
                max: T::MAX_BIT_OFFSET,
            });
        }
        Ok(Self {
            pos: p,
            phantomdata: PhantomData,
        })
    }
}

/// range of bits in a type `T` which implements the `Bits`
/// trait, from the offset `start` up to and including the
/// bit at offset `end`.
/// ensures the validity of the range during creation.
#[derive(Clone, Copy)]
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

    /// shift left value used to set all hi bits
    /// for the mask to extract the range from the `MAX_MASK`
    /// of the type `T` to `0`
    pub(crate) fn mask_lshift(&self) -> usize {
        T::MAX_BIT_OFFSET - self.end
    }

    /// shift right value used to set all lo bits
    /// of the `mask_lshift` to
    pub(crate) fn mask_rshift(&self) -> usize {
        self.mask_lshift() + self.start
    }
}

/// a single bit at position `pos` can be read from every type
/// which implements the `Bits` trait.
pub trait ReadableBit: Bits {
    fn read_bit(&self, pos: BitOffset<Self>) -> u8;
}

macro_rules! impl_readable_bit {
    ($s:ty) => {
        impl ReadableBit for $s {
            fn read_bit(&self, pos: BitOffset<$s>) -> u8 {
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
    fn set_bit(&mut self, pos: BitOffset<Self>);
}

macro_rules! impl_setable_bit {
    ($s:ty) => {
        impl SetableBit for $s {
            fn set_bit(&mut self, pos: BitOffset<$s>) {
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
impl_setable_bits!(u32);
impl_setable_bits!(u64);

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

/// read primitive number types from byte array
/// with little endian ordering
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
        BigEndian, BitOffset, BitRange, BitsReadableAs, LittleEndian, ReadableBit, ReadsFromBytes,
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
        let pos_4_u8 = BitOffset::<u8>::new(4).unwrap();
        let pos_3_u8 = BitOffset::<u8>::new(3).unwrap();
        assert_eq!(val_u8.read_bit(pos_4_u8), 1);
        assert_eq!(val_u8.read_bit(pos_3_u8), 0);
        let pos_8_u16 = BitOffset::<u16>::new(8).unwrap();
        let val_u16: u16 = 0x0100;
        assert_eq!(val_u16.read_bit(pos_8_u16), 1);
        let pos_16_u32 = BitOffset::<u32>::new(16).unwrap();
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
        let val_u64: u64 = 0x0011223344556677;
        assert_eq!(
            LittleEndian::read_from_u64(val_u64),
            [0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00]
        );
    }

    #[test]
    fn read_from_bytes_be() {
        let val_u16: [u8; 2] = [0xAA, 0xBB];
        assert_eq!(BigEndian::read_into_u16(val_u16), 0xAABB);
        let val_u32: [u8; 4] = [0xAA, 0xBB, 0xCC, 0xDD];
        assert_eq!(BigEndian::read_into_u32(val_u32), 0xAABBCCDD);
        let val_u64: [u8; 8] = [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        assert_eq!(BigEndian::read_into_u64(val_u64), 0x0011223344556677)
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
        );
    }

    #[test]
    fn bit_offset_validation() {
        let invalid_u8 = BitOffset::<u8>::new(8);
        assert!(invalid_u8.is_err());
        let invalid_u16 = BitOffset::<u16>::new(16);
        assert!(invalid_u16.is_err());
        let invalid_u32 = BitOffset::<u32>::new(32);
        assert!(invalid_u32.is_err());
        let invalid_u64 = BitOffset::<u64>::new(64);
        assert!(invalid_u64.is_err())
    }

    #[test]
    fn set_bit() {
        let offset_2_u8 = BitOffset::<u8>::new(2).unwrap();
        let mut val_u8: u8 = 0;
        val_u8.set_bit(offset_2_u8);
        assert_eq!(val_u8, 4);
        let offset_8_u16 = BitOffset::<u16>::new(8).unwrap();
        let mut val_u16 = 0u16;
        val_u16.set_bit(offset_8_u16);
        assert_eq!(val_u16, 256)
    }

    #[test]
    fn set_bits() {
        let mut val_u8 = 0u8;
        let r_u8 = BitRange::<u8>::new(1, 3).unwrap();
        val_u8.set_bits(r_u8);
        assert_eq!(val_u8, 14);
        let mut val_u16 = 0u16;
        let r_u16 = BitRange::<u16>::new(8, 15).unwrap();
        val_u16.set_bits(r_u16);
        assert_eq!(val_u16, 0xFF00)
    }
}
