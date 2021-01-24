#![feature(unsize)]

//! Let's create a thin pointer!
//!
//! Most of the credit goes to Simon Sapin; this is just an adapted version of what RFC 2580 lays out.

mod thin {

use std::{
    alloc::{self, Layout},
    fmt::{self, Debug, Formatter},
    marker::{PhantomData, Unsize},
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};
use rfc2580::{self, AlignedMetaData, Pointee};

/// ThinBox.
///
/// A thin pointer, regardless of T.
pub struct ThinBox<T: ?Sized + Pointee>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    ptr: NonNull<WithMeta<<T as Pointee>::MetaData, ()>>,
    _marker: PhantomData<fn(T) -> T>,
}

impl<T: Pointee> ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    pub fn new(value: T) -> Self {
        let meta = rfc2580::into_raw_parts(&value as *const T).0;
        let ptr = NonNull::from(Box::leak(Box::new(WithMeta{ meta, value, }))).cast();
        ThinBox { ptr, _marker: PhantomData }
    }
}

impl<T: ?Sized + Pointee> ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    pub fn new_unsize<S>(value: S) -> Self
        where S: Unsize<T>
    {
        let meta = rfc2580::into_raw_parts(&value as &T as *const T).0;
        let ptr = NonNull::from(Box::leak(Box::new(WithMeta{ meta, value }))).cast();
        ThinBox { ptr, _marker: PhantomData }
    }
}

impl<T: ?Sized + Debug + Pointee> Debug for ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &*self)
    }
}

impl<T: ?Sized + Pointee> Deref for ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    type Target = T;

    fn deref(&self) -> &T {
        let pointer = rfc2580::from_raw_parts(self.meta(), self.data());
        unsafe {
            &*pointer
        }
    }
}

impl<T: ?Sized + Pointee> DerefMut for ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    fn deref_mut(&mut self) -> &mut T {
        let pointer = rfc2580::from_raw_parts(self.meta(), self.data()) as *mut T;
        unsafe {
            &mut *pointer
        }
    }
}

impl<T: ?Sized + Pointee> Drop for ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    fn drop(&mut self) {
        unsafe {
            let value: &mut T = &mut *self;
            let layout = Layout::from_size_align_unchecked(mem::size_of_val(value), mem::align_of_val(value));
            ptr::drop_in_place::<T>(value as *mut T);
            alloc::dealloc(self.ptr.cast().as_ptr(), layout);
        }
    }
}

//
//  Implementation details.
//
impl<T: ?Sized + Pointee> ThinBox<T>
    where
        <T as Pointee>::MetaData: AlignedMetaData,
{
    fn meta(&self) -> <T as Pointee>::MetaData {
        unsafe { self.ptr.as_ref() }.meta
    }

    fn data(&self) -> *const u8 {
        unsafe {
            let offset = std::mem::size_of::<<T as Pointee>::MetaData>();
            let value_align = self.meta().align();
            let offset = align_up_to(offset, value_align);
            (self.ptr.as_ptr() as *const u8).add(offset)
        }
    }
}

#[repr(C)]
struct WithMeta<Meta: AlignedMetaData, Data> {
    meta: Meta,
    value: Data,
}

/// <https://github.com/rust-lang/rust/blob/1.30.0/src/libcore/alloc.rs#L199-L219>
fn align_up_to(offset: usize, align: usize) -> usize {
    offset.wrapping_add(align).wrapping_sub(1) & !align.wrapping_sub(1)
}

}   //  mod thin.

use std::mem;

use thin::ThinBox;

//
//  Showing it off.
//
fn main() {
    {
        let thin = ThinBox::new(42i32);

        assert_eq!(mem::size_of::<*const i32>(), mem::size_of_val(&thin));

        println!("{:?}", thin);
    }
    {
        let thin_slice = ThinBox::<[i32]>::new_unsize([1, 2, 3, 4]);

        assert_eq!(mem::size_of::<*const i32>(), mem::size_of_val(&thin_slice));

        println!("{:?}", thin_slice);
    }
}
