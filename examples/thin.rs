#![feature(unsize)]

//! Let's create a thin pointer!
//!
//! This is a completely different design that the one in the RFC, using a middle-pointer.

mod thin {

use std::{
    alloc::{self, Layout},
    cmp,
    fmt::{self, Debug, Formatter},
    marker::{PhantomData, Unsize},
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};
use rfc2580::{self, Pointee};

/// ThinBox.
///
/// A thin pointer, regardless of T.
pub struct ThinBox<T: ?Sized + Pointee> {
    ptr: WithHeader<T::MetaData>,
    _marker: PhantomData<fn(T) -> T>,
}

impl<T: Pointee> ThinBox<T> {
    pub fn new(value: T) -> Self {
        let meta = rfc2580::into_raw_parts(&value as *const T).0;
        let ptr = WithHeader::new(meta, value).expect("No allocation failure");
        ThinBox { ptr, _marker: PhantomData }
    }
}

impl<T: ?Sized + Pointee> ThinBox<T> {
    pub fn new_unsize<S>(value: S) -> Self
        where S: Unsize<T>
    {
        let meta = rfc2580::into_raw_parts(&value as &T as *const T).0;
        let ptr = WithHeader::new(meta, value).expect("No allocation failure");
        ThinBox { ptr, _marker: PhantomData }
    }
}

impl<T: ?Sized + Debug + Pointee> Debug for ThinBox<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &*self)
    }
}

impl<T: ?Sized + Pointee> Deref for ThinBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        let pointer = rfc2580::from_raw_parts(self.meta(), self.data());
        unsafe {
            &*pointer
        }
    }
}

impl<T: ?Sized + Pointee> DerefMut for ThinBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        let pointer = rfc2580::from_raw_parts(self.meta(), self.data()) as *mut T;
        unsafe {
            &mut *pointer
        }
    }
}

impl<T: ?Sized + Pointee> Drop for ThinBox<T> {
    fn drop(&mut self) {
        unsafe {
            let value: &mut T = &mut *self;
            let value: *mut T = value as *mut T;
            self.ptr.drop::<T>(value);
        }
    }
}

//
//  Implementation details.
//
impl<T: ?Sized + Pointee> ThinBox<T> {
    fn meta(&self) -> T::MetaData {
        //  Safety:
        //  -   NonNull and valid.
        unsafe { *self.ptr.header().as_ptr() }
    }

    fn data(&self) -> *const u8 { self.ptr.value().as_ptr() as *const u8 }
}

struct WithHeader<H>(NonNull<u8>, PhantomData<H>);

impl<H> WithHeader<H> {
    fn new<T>(header: H, value: T) -> Option<WithHeader<H>> {
        let layout = Self::alloc_layout(mem::size_of::<T>(), mem::align_of::<T>());
        let aligned_header_size = Self::aligned_header_size(layout.align());

        unsafe {
            let ptr = NonNull::new(alloc::alloc(layout))?;

            //  Safety:
            //  -   The size is at least `aligned_header_size`.
            let ptr = NonNull::new_unchecked(ptr.as_ptr().offset(aligned_header_size as isize));

            let result = WithHeader(ptr, PhantomData);
            ptr::write(result.header().as_ptr(), header);
            ptr::write(result.value().as_ptr().cast(), value);

            Some(result)
        }
    }

    //  Safety:
    //  -   Assumes that `value` can be dereferenced.
    unsafe fn drop<T: ?Sized>(&self, value: *mut T) {
        let layout = Self::alloc_layout(mem::size_of_val(&*value), mem::align_of_val(&*value));
        let aligned_header_size = Self::aligned_header_size(layout.align());

        ptr::drop_in_place::<T>(value as *mut T);
        alloc::dealloc(self.0.as_ptr().offset(-(aligned_header_size as isize)), layout);

    }

    fn header(&self) -> NonNull<H> {
        //  Safety:
        //  -   At least `size_of::<H>()` bytes are allocated ahead of the pointer.
        unsafe { NonNull::new_unchecked(self.0.as_ptr().offset(-(Self::header_size() as isize)) as *mut H) }
    }

    fn value(&self) -> NonNull<u8> { self.0 }

    //
    //  Implementation Details
    //

    fn header_size() -> usize { mem::size_of::<H>() }

    fn alloc_layout(value_size: usize, value_align: usize) -> Layout {
        assert!(Self::header_size() <= usize::MAX / 2 + 1);

        let alloc_align = cmp::max(mem::align_of::<H>(), value_align);
        let alloc_size = Self::aligned_header_size(alloc_align) + value_size;

        //  Safety:
        //  -   `align` is not zero and a power of two, as guaranteed by `mem::align_of`.
        //  -   The size can be rounded up to `align` without overflow, or `H` is way too big.
        unsafe { Layout::from_size_align_unchecked(alloc_size, alloc_align) }
    }

    fn aligned_header_size(alloc_align: usize) -> usize { cmp::max(Self::header_size(), alloc_align) }
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
