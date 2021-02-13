#![no_std]
#![feature(raw)]
#![feature(specialization)]

#![allow(incomplete_features)]
#![deny(missing_docs)]

//! An (extended) implementation of the proposal of [RFC 2580](https://github.com/rust-lang/rfcs/pull/2580).
//!
//! #   Purpose.
//!
//! The purpose of this crate is dual:
//!
//! 1.  The ability to take apart a fat pointer, and put it back together later.
//! 2.  The ability to do so for any pointer, be it a pointer to trait, slice, or a regular `Sized` type.
//!
//! The second ability, in particular, is not brushed upon by RFC 2580 as far as I can tell, yet is critical in
//! enabling uniform handling of `*const T` regardless of the nature of `T`.
//!
//! #   Usage.
//!
//! The traits defined by this crate -- `Pointee` and `MetaData` -- are already implemented for all types, and are
//! generally not expected to be used by themselves apart from bounds.
//!
//! Instead, the high-level API of this crate are the two functions:
//!
//! -   `into_raw_parts`, which splits a pointer into meta-data and pointer-to-data parts.
//! -   `from_raw_parts`, which joins back the two parts to recreate a (possibly fat) pointer.
//!
//! #   Safety.
//!
//! This crate operates entirely in terms of pointers; the operations it performs are safe even in the presence of
//! dangling pointers, or null pointers.
//!
//! In return, whether the pointers it recreates are safe to dereference or not hinges entirely on whether the pointer
//! to data used to recreate the full pointer is safe to dereference.
//!
//! #   Example.
//!
//! A simple example showing how to take apart a pointer and recreate it.
//!
//! ```
//! use rfc2580::{from_raw_parts, into_raw_parts};
//!
//! let mut array = [1; 4];
//! let slice = &mut array[..];
//! let (meta, data) = into_raw_parts(slice as *mut [i32]);
//!
//! let reconstituted = from_raw_parts(meta, data);
//!
//! assert_eq!(slice as *mut [i32], reconstituted);
//! ```

use core::{marker::PhantomData, mem, ptr::NonNull, raw::TraitObject};

/// SizedMetaData.
///
/// The meta-data information associated to a pointer to a Sized T.
///
/// This is a Zero-Sized Type, as there is no such meta-data information. It is useful for uniform handling of T
/// regardless of sizedness.
pub struct SizedMetaData<T>(PhantomData<fn(T) -> T>);

impl<T> Clone for SizedMetaData<T> {
    fn clone(&self) -> Self { *self }
}

impl<T> Copy for SizedMetaData<T> {}


/// DynMetaData.
///
/// The meta-data information associated to a pointer to a trait object.
pub struct DynMetaData<T: ?Sized>(*mut (), PhantomData<fn(T) -> T>);

impl<T: ?Sized> Clone for DynMetaData<T> {
    fn clone(&self) -> Self { *self }
}

impl<T: ?Sized> Copy for DynMetaData<T> {}


/// SliceMetaData.
///
/// The meta-data information associated to a pointer to a slice object.
pub struct SliceMetaData<T: ?Sized>(usize, PhantomData<fn(T) -> T>);

impl<T: ?Sized> Clone for SliceMetaData<T> {
    fn clone(&self) -> Self { *self }
}

impl<T: ?Sized> Copy for SliceMetaData<T> {}


/// MetaData.
///
/// A trait representing the MetaData associated to a pointer.
pub trait MetaData: Sized {
    /// The type of the pointee of which `self` represents the meta-data.
    type Pointee : ?Sized;

    /// Joins a meta-data and data-pointer parts into a pointer to the appropriate type.
    fn assemble(&self, data: *mut u8) -> *mut Self::Pointee;

    /// Splits any pointer into its meta-data and data-pointer parts.
    fn disassemble(ptr: *mut Self::Pointee) -> (Self, *mut u8);
}

impl<T: ?Sized> MetaData for DynMetaData<T> {
    type Pointee = T;

    fn assemble(&self, data: *mut u8) -> *mut T {
        assert!(mem::size_of::<*mut T>() == mem::size_of::<TraitObject>());

        let object = TraitObject { data: data as *mut (), vtable: self.0 as *mut () };

        unsafe { mem::transmute_copy(&object) }
    }

    fn disassemble(ptr: *mut T) -> (Self, *mut u8) {
        assert!(mem::size_of::<*mut T>() == mem::size_of::<(usize, usize)>());

        let object: TraitObject = unsafe { mem::transmute_copy(&ptr) };

        (DynMetaData(object.vtable, PhantomData), object.data as *mut u8)
    }
}

//  The slice specialization. It is dodgy, avoiding the use of from_raw_parts to
//  avoid materializing a reference in case the pointer is dangling or null.
impl<T> MetaData for SliceMetaData<T> {
    type Pointee = [T];

    fn assemble(&self, data: *mut u8) -> *mut [T] {
        debug_assert!(mem::size_of::<*mut [T]>() == mem::size_of::<(usize, usize)>());

        unsafe { mem::transmute_copy(&(data, self.0)) }
    }

    fn disassemble(ptr: *mut [T]) -> (Self, *mut u8) {
        debug_assert!(mem::size_of::<*mut [T]>() == mem::size_of::<(usize, usize)>());

        let (data, len): (usize, usize) = unsafe { mem::transmute_copy(&ptr) };

        (SliceMetaData(len, PhantomData), data as *mut u8)
    }
}

impl<T> MetaData for SizedMetaData<T> {
    type Pointee = T;

    fn assemble(&self, data: *mut u8) -> *mut T {
        data as *mut T
    }

    fn disassemble(ptr: *mut T) -> (Self, *mut u8) {
        (SizedMetaData(PhantomData), ptr as *mut u8)
    }
}


/// Pointee.
///
/// A trait associating the appropriate meta-data to a given pointer type.
pub trait Pointee {
    /// The type of the meta-data associated to pointers to `Self`.
    type MetaData: MetaData<Pointee = Self> + Clone + Copy;
}

impl<T: ?Sized> Pointee for T {
    default type MetaData = DynMetaData<T>;
}

impl<T> Pointee for [T] {
    type MetaData = SliceMetaData<T>;
}

impl<T> Pointee for T {
    type MetaData = SizedMetaData<T>;
}


/// Splits any pointer into its meta-data and data-pointer parts.
///
/// For the `NonNull` equivalent, see `into_non_null_parts`.
///
/// #   Examples
///
/// ```
/// use rfc2580::into_raw_parts;
///
/// let array = [1; 4];
/// let slice = &array[..];
/// let (meta, data) = into_raw_parts(slice as *const [i32] as *mut [i32]);
///
/// assert_eq!(slice.as_ptr() as *mut u8, data);
/// ```
pub fn into_raw_parts<T: ?Sized + Pointee>(ptr: *mut T) -> (<T as Pointee>::MetaData, *mut u8) {
    <T as Pointee>::MetaData::disassemble(ptr)
}


/// Joins a meta-data and data-pointer parts into a pointer to the appropriate type.
///
/// For the `NonNull` equivalent, see `from_non_null_parts`.
///
/// #   Examples
///
/// ```
/// use rfc2580::{from_raw_parts, into_raw_parts};
///
/// let array = [1; 4];
/// let slice = &array[..];
/// let (meta, data) = into_raw_parts(slice as *const [i32] as *mut [i32]);
///
/// let reconstituted = from_raw_parts(meta, data);
///
/// assert_eq!(slice as *const [i32] as *mut [i32], reconstituted);
/// ```
pub fn from_raw_parts<T: ?Sized, M: MetaData<Pointee = T>>(meta: M, ptr: *mut u8) -> *mut T {
    meta.assemble(ptr)
}


/// Splits any pointer into its meta-data and data-pointer parts.
///
/// For the raw pointer equivalent, see `into_raw_parts`.
///
/// #   Examples
///
/// ```
/// use core::ptr::NonNull;
/// use rfc2580::into_non_null_parts;
///
/// let mut array = [1; 4];
/// let (meta, data) = into_non_null_parts(NonNull::from(&mut array[..]));
///
/// assert_eq!(NonNull::from(&mut array[..]).cast(), data);
/// ```
pub fn into_non_null_parts<T: ?Sized + Pointee>(ptr: NonNull<T>) -> (<T as Pointee>::MetaData, NonNull<u8>) {
    let (meta, ptr) = into_raw_parts(ptr.as_ptr());
    //  Safety:
    //  -   `ptr` is non-null, hence the result is non-null.
    (meta, unsafe { NonNull::new_unchecked(ptr) })
}


/// Joins a meta-data and data-pointer parts into a pointer to the appropriate type.
///
/// For the raw pointer equivalent, see `from_raw_parts`.
///
/// #   Examples
///
/// ```
/// use core::ptr::NonNull;
/// use rfc2580::{from_non_null_parts, into_non_null_parts};
///
/// let mut array = [1; 4];
/// let (meta, data) = into_non_null_parts(NonNull::from(&mut array[..]));
///
/// let reconstituted = from_non_null_parts(meta, data);
///
/// assert_eq!(NonNull::from(&mut array[..]), reconstituted);
/// ```
pub fn from_non_null_parts<T: ?Sized, M: MetaData<Pointee = T>>(meta: M, ptr: NonNull<u8>) -> NonNull<T> {
    //  Safety:
    //  -   `ptr` is non-null, hence the result is non-null.
    unsafe { NonNull::new_unchecked(from_raw_parts(meta, ptr.as_ptr())) }
}


#[cfg(test)]
mod tests {

use core::fmt::Debug;

use super::*;

const SIZE_OF_USIZE: usize = mem::size_of::<usize>();

#[test]
fn split_join_sized() {
    let item = 42i32;
    let ptr = &item as *const _ as *mut _;

    let (meta, data) = into_raw_parts(ptr);

    assert_eq!(0, mem::size_of_val(&meta));
    assert_eq!(ptr, data as *mut i32);

    let phoenix = from_raw_parts(meta, data);

    assert_eq!(ptr, phoenix);
}

#[test]
fn split_join_slice() {
    let array = [1, 2, 3, 4];
    let slice = &array[..];
    let ptr = slice as *const [i32] as *mut [i32];

    let (meta, data) = into_raw_parts(ptr);

    assert_eq!(SIZE_OF_USIZE, mem::size_of_val(&meta));
    assert_eq!(slice.as_ptr(), data as *mut i32);

    let phoenix = from_raw_parts(meta, data);

    assert_eq!(ptr, phoenix);
}

#[test]
fn split_join_trait() {
    let item = 42i32;
    let debug = &item as &dyn Debug;
    let ptr = debug as *const dyn Debug as *mut dyn Debug;

    let (meta, data) = into_raw_parts(ptr);

    assert_eq!(SIZE_OF_USIZE, mem::size_of_val(&meta));

    let phoenix = from_raw_parts(meta, data);

    assert_eq!(ptr, phoenix);
}

}
