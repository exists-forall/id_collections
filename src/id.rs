//! The [`Id`](trait@Id) trait and related traits.

use std::fmt::{Debug, Display};

use num_traits::{PrimInt, Unsigned};

/// A trait for converting from integer types without bounds checking.
///
/// This trait is intended to be implemented only by primitive unsigned integer types. You probably
/// do not need to implement this trait yourself.
///
/// This is a low-level trait intended to make it possible to write efficient implementations of
/// structures like [`IdVec<I, T>`](crate::IdVec) which frequently convert between [`Id`] types and primitive
/// integer types internally.
///
/// # Safety and Panics
///
/// For each conversion function in this trait, it is the caller's responsibility to ensure that the
/// provided value is *in bounds* for `Self`. If the provided value is not representable as a value
/// of `Self`, the conversion function is allowed to *either*:
/// 1. panic
/// 2. perform the conversion via two's-complement wrapping
///
/// In practice, the current behavior of each conversion function is to panic when debug assertions
/// are enabled, and to wrap in release builds. This is not guaranteed to remain true in the future.
///
/// # Examples
///
/// ```
/// use id_collections::id::FromPrimIntUnchecked;
///
/// assert_eq!(u32::from_i64_unchecked(10), 10);
/// ```
///
/// ```no_run
/// use id_collections::id::FromPrimIntUnchecked;
///
/// // may panic (in debug builds), or may return '0xFE' (in release builds):
/// let value = u8::from_u32_unchecked(0xCA7CAFE);
/// ```
pub trait FromPrimIntUnchecked {
    fn from_i8_unchecked(n: i8) -> Self;
    fn from_i16_unchecked(n: i16) -> Self;
    fn from_i32_unchecked(n: i32) -> Self;
    fn from_i64_unchecked(n: i64) -> Self;
    fn from_i128_unchecked(n: i128) -> Self;
    fn from_isize_unchecked(n: isize) -> Self;
    fn from_u8_unchecked(n: u8) -> Self;
    fn from_u16_unchecked(n: u16) -> Self;
    fn from_u32_unchecked(n: u32) -> Self;
    fn from_u64_unchecked(n: u64) -> Self;
    fn from_u128_unchecked(n: u128) -> Self;
    fn from_usize_unchecked(n: usize) -> Self;
}

macro_rules! impl_from_prim_int_unchecked_method {
    ($name:ident, $src_ty:ty, $dst_ty:ty) => {
        fn $name(n: $src_ty) -> Self {
            if cfg!(debug_assertions) {
                match n.try_into() {
                    Ok(value) => value,
                    Err(err) => {
                        panic!("{}::{}: {}", stringify!($dst_ty), stringify!($name), err);
                    }
                }
            } else {
                n as $dst_ty
            }
        }
    };
}

macro_rules! impl_from_prim_int_unchecked {
    ($dst_ty:ty) => {
        impl FromPrimIntUnchecked for $dst_ty {
            impl_from_prim_int_unchecked_method!(from_i8_unchecked, i8, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_i16_unchecked, i16, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_i32_unchecked, i32, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_i64_unchecked, i64, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_i128_unchecked, i128, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_isize_unchecked, isize, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_u8_unchecked, u8, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_u16_unchecked, u16, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_u32_unchecked, u32, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_u64_unchecked, u64, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_u128_unchecked, u128, $dst_ty);
            impl_from_prim_int_unchecked_method!(from_usize_unchecked, usize, $dst_ty);
        }
    };
}

impl_from_prim_int_unchecked!(u8);
impl_from_prim_int_unchecked!(u16);
impl_from_prim_int_unchecked!(u32);
impl_from_prim_int_unchecked!(u64);
impl_from_prim_int_unchecked!(u128);
impl_from_prim_int_unchecked!(usize);

/// A trait for converting to integer types without bounds checking.
///
/// This trait is intended to be implemented only by primitive unsigned integer types. You probably
/// do not need to implement this trait yourself.
///
/// This is a low-level trait intended to make it possible to write efficient implementations of
/// structures like [`IdVec<I, T>`](crate::IdVec) which frequently convert between [`Id`] types and primitive
/// integer types internally.
///
/// # Safety and Panics
///
/// For each conversion function in this trait, it is the caller's responsibility to ensure that the
/// provided value is *in bounds* for the target type. If the provided value is not representable as
/// a value of the target type, the conversion function is allowed to *either*:
/// 1. panic
/// 2. perform the conversion via two's-complement wrapping
///
/// In practice, the current behavior of each conversion function is to panic when debug assertions
/// are enabled, and to wrap in release builds. This is not guaranteed to remain true in the future.
///
/// # Examples
///
/// ```
/// use id_collections::id::ToPrimIntUnchecked;
///
/// assert_eq!(10u64.to_u32_unchecked(), 10);
/// ```
///
/// ```no_run
/// use id_collections::id::ToPrimIntUnchecked;
///
/// // may panic (in debug builds), or may return '0xFE' (in release builds):
/// let value = 0xCA7CAFEu32.to_u8_unchecked();
/// ```
pub trait ToPrimIntUnchecked {
    fn to_i8_unchecked(self) -> i8;
    fn to_i16_unchecked(self) -> i16;
    fn to_i32_unchecked(self) -> i32;
    fn to_i64_unchecked(self) -> i64;
    fn to_i128_unchecked(self) -> i128;
    fn to_isize_unchecked(self) -> isize;
    fn to_u8_unchecked(self) -> u8;
    fn to_u16_unchecked(self) -> u16;
    fn to_u32_unchecked(self) -> u32;
    fn to_u64_unchecked(self) -> u64;
    fn to_u128_unchecked(self) -> u128;
    fn to_usize_unchecked(self) -> usize;
}

macro_rules! impl_to_prim_int_unchecked_method {
    ($name:ident, $src_ty:ty, $dst_ty:ty) => {
        fn $name(self) -> $dst_ty {
            if cfg!(debug_assertions) {
                match self.try_into() {
                    Ok(value) => value,
                    Err(err) => {
                        panic!("{}::{}: {}", stringify!($src_ty), stringify!($name), err);
                    }
                }
            } else {
                self as $dst_ty
            }
        }
    };
}

macro_rules! impl_to_prim_int_unchecked {
    ($src_ty:ty) => {
        impl ToPrimIntUnchecked for $src_ty {
            impl_to_prim_int_unchecked_method!(to_i8_unchecked, $src_ty, i8);
            impl_to_prim_int_unchecked_method!(to_i16_unchecked, $src_ty, i16);
            impl_to_prim_int_unchecked_method!(to_i32_unchecked, $src_ty, i32);
            impl_to_prim_int_unchecked_method!(to_i64_unchecked, $src_ty, i64);
            impl_to_prim_int_unchecked_method!(to_i128_unchecked, $src_ty, i128);
            impl_to_prim_int_unchecked_method!(to_isize_unchecked, $src_ty, isize);
            impl_to_prim_int_unchecked_method!(to_u8_unchecked, $src_ty, u8);
            impl_to_prim_int_unchecked_method!(to_u16_unchecked, $src_ty, u16);
            impl_to_prim_int_unchecked_method!(to_u32_unchecked, $src_ty, u32);
            impl_to_prim_int_unchecked_method!(to_u64_unchecked, $src_ty, u64);
            impl_to_prim_int_unchecked_method!(to_u128_unchecked, $src_ty, u128);
            impl_to_prim_int_unchecked_method!(to_usize_unchecked, $src_ty, usize);
        }
    };
}

impl_to_prim_int_unchecked!(u8);
impl_to_prim_int_unchecked!(u16);
impl_to_prim_int_unchecked!(u32);
impl_to_prim_int_unchecked!(u64);
impl_to_prim_int_unchecked!(u128);
impl_to_prim_int_unchecked!(usize);

/// A trait for custom strongly-typed wrappers around integer types.
///
/// A type which implements `Id` can be used as the index type for an [`IdVec<I, T>`](crate::IdVec),
/// or as the key type for an [`IdMap<I, T>`](crate::IdMap).
///
/// The most convenient way to implement the `Id` trait for your own types is to use the
/// [`#[id_type]`](crate::id_type) attribute macro:
///
/// ```
/// use id_collections::{Id, id_type};
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct UserId(u32);
///
/// // 'UserId implements 'Id':
/// assert_eq!(UserId(10).to_index(), 10);
/// assert_eq!(UserId::from_index(10), UserId(10));
/// ```
///
/// Using the [`#[id_type]`](crate::id_type) macro will automatically derive `Id`, as well as all
/// the standard library traits which `Id` requires, like [`Clone`], [`Copy`], [`Eq`], etc. You can
/// also derive the [`Id`](macro@crate::Id) trait on its own, and separately derive the other traits
/// which it requires:
///
/// ```
/// use id_collections::Id;
///
/// #[derive(Id, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct UserId(u32);
///
/// assert_eq!(UserId(10).to_index(), 10);
/// assert_eq!(UserId::from_index(10), UserId(10));
/// ```
///
/// The `Id` trait is primarily intended to be implemented by custom struct types. However, you can
/// also use any built-in primitive unsigned integer type, like [`u32`] or [`usize`], as an `Id`:
///
/// ```
/// use id_collections::Id;
///
/// assert_eq!(10u32.to_index(), 10u32);
/// assert_eq!(u32::from_index(10), 10u32);
/// ```
pub trait Id: Sized + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + std::hash::Hash {
    /// The underlying unsigned integer type wrapped by `Self`.
    type Index: PrimInt + Unsigned + FromPrimIntUnchecked + ToPrimIntUnchecked + Debug + Display;

    /// Constructs a value of `Self` from its underlying integer type.
    fn from_index(index: Self::Index) -> Self;

    /// Converts a value of `Self` to its underlying integer type.
    fn to_index(self) -> Self::Index;
}

macro_rules! impl_id {
    ($id_ty:ty) => {
        impl Id for $id_ty {
            type Index = $id_ty;
            fn from_index(index: Self::Index) -> Self {
                index
            }
            fn to_index(self) -> Self::Index {
                self
            }
        }
    };
}

impl_id!(u8);
impl_id!(u16);
impl_id!(u32);
impl_id!(u64);
impl_id!(u128);
impl_id!(usize);
