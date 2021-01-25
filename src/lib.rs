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
//! let array = [1; 4];
//! let slice = &array[..];
//! let (meta, data) = into_raw_parts(slice as *const [i32]);
//!
//! let reconstituted = from_raw_parts(meta, data);
//!
//! assert_eq!(slice as *const [i32], reconstituted);
//! ```

use core::{marker::PhantomData, mem, raw::TraitObject};

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
    fn assemble(&self, data: *const u8) -> *const Self::Pointee;

    /// Splits any pointer into its meta-data and data-pointer parts.
    fn disassemble(ptr: *const Self::Pointee) -> (Self, *const u8);
}

impl<T: ?Sized> MetaData for DynMetaData<T> {
    type Pointee = T;

    fn assemble(&self, data: *const u8) -> *const T {
        assert!(mem::size_of::<*const T>() == mem::size_of::<TraitObject>());

        let object = TraitObject { data: data as *mut (), vtable: self.0 as *mut () };

        unsafe { mem::transmute_copy(&object) }
    }

    fn disassemble(ptr: *const T) -> (Self, *const u8) {
        assert!(mem::size_of::<*const T>() == mem::size_of::<(usize, usize)>());

        let object: TraitObject = unsafe { mem::transmute_copy(&ptr) };

        (DynMetaData(object.vtable, PhantomData), object.data as *const u8)
    }
}

//  The slice specialization. It is dodgy, avoiding the use of from_raw_parts to
//  avoid materializing a reference in case the pointer is dangling or null.
impl<T> MetaData for SliceMetaData<T> {
    type Pointee = [T];

    fn assemble(&self, data: *const u8) -> *const [T] {
        debug_assert!(mem::size_of::<*const [T]>() == mem::size_of::<(usize, usize)>());

        unsafe { mem::transmute_copy(&(data, self.0)) }
    }

    fn disassemble(ptr: *const [T]) -> (Self, *const u8) {
        debug_assert!(mem::size_of::<*const [T]>() == mem::size_of::<(usize, usize)>());

        let (data, len): (usize, usize) = unsafe { mem::transmute_copy(&ptr) };

        (SliceMetaData(len, PhantomData), data as *const u8)
    }
}

impl<T> MetaData for SizedMetaData<T> {
    type Pointee = T;

    fn assemble(&self, data: *const u8) -> *const T {
        data as *const T
    }

    fn disassemble(ptr: *const T) -> (Self, *const u8) {
        (SizedMetaData(PhantomData), ptr as *const u8)
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
/// #   Examples
///
/// ```
/// use rfc2580::into_raw_parts;
///
/// let array = [1; 4];
/// let slice = &array[..];
/// let (meta, data) = into_raw_parts(slice as *const [i32]);
///
/// assert_eq!(slice.as_ptr() as *const u8, data);
/// ```
pub fn into_raw_parts<T: ?Sized + Pointee>(ptr: *const T) -> (<T as Pointee>::MetaData, *const u8) {
    <T as Pointee>::MetaData::disassemble(ptr)
}


/// Joins a meta-data and data-pointer parts into a pointer to the appropriate type.
///
/// #   Examples
///
/// ```
/// use rfc2580::{from_raw_parts, into_raw_parts};
///
/// let array = [1; 4];
/// let slice = &array[..];
/// let (meta, data) = into_raw_parts(slice as *const [i32]);
///
/// let reconstituted = from_raw_parts(meta, data);
///
/// assert_eq!(slice as *const [i32], reconstituted);
/// ```
pub fn from_raw_parts<T: ?Sized, M: MetaData<Pointee = T>>(meta: M, ptr: *const u8) -> *const T {
    meta.assemble(ptr)
}


#[cfg(test)]
mod tests {

use core::fmt::Debug;

use super::*;

const SIZE_OF_USIZE: usize = mem::size_of::<usize>();

#[test]
fn split_join_sized() {
    let item = 42i32;
    let ptr = &item as *const _;

    let (meta, data) = into_raw_parts(ptr);

    assert_eq!(0, mem::size_of_val(&meta));
    assert_eq!(ptr, data as *const i32);

    let phoenix = from_raw_parts(meta, data);

    assert_eq!(ptr, phoenix);
}

#[test]
fn split_join_slice() {
    let array = [1, 2, 3, 4];
    let slice = &array[..];
    let ptr = slice as *const [i32];

    let (meta, data) = into_raw_parts(ptr);

    assert_eq!(SIZE_OF_USIZE, mem::size_of_val(&meta));
    assert_eq!(slice.as_ptr(), data as *const i32);

    let phoenix = from_raw_parts(meta, data);

    assert_eq!(ptr, phoenix);
}

#[test]
fn split_join_trait() {
    let item = 42i32;
    let debug = &item as &dyn Debug;
    let ptr = debug as *const dyn Debug;

    let (meta, data) = into_raw_parts(ptr);

    assert_eq!(SIZE_OF_USIZE, mem::size_of_val(&meta));

    let phoenix = from_raw_parts(meta, data);

    assert_eq!(ptr, phoenix);
}

}
