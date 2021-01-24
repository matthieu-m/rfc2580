An (extended) implementation of the proposal of [RFC 2580](https://github.com/rust-lang/rfcs/pull/2580).

#   Purpose.

The purpose of this crate is dual:

1.  The ability to take apart a fat pointer, and put it back together later.
2.  The ability to do so for any pointer, be it a pointer to trait, slice, or a regular `Sized` type.

The second ability, in particular, is not brushed upon by RFC 2580 as far as I can tell, yet is critical in
enabling uniform handling of `*const T` regardless of the nature of `T`.

This uniform handling vastly simplifies the implementation of custom storage, such as `ThinBox` presented in the `thin`
example. Most specifically, the uniform handling allows an implementation of `ThinBox` NOT to use specialization, an
unstable feature with no stabilization date in sight.

#   Usage.

The traits defined by this crate -- `Pointee` and `MetaData` -- are already implemented for all types, and are
generally not expected to be used by themselves apart from bounds.

Instead, the high-level API of this crate are the two functions:

-   `into_raw_parts`, which splits a pointer into meta-data and pointer-to-data parts.
-   `from_raw_parts`, which joins back the two parts to recreate a (possibly fat) pointer.

#   Safety.

This crate operates entirely in terms of pointers; the operations it performs are safe even in the presence of
dangling pointers, or null pointers.

In return, whether the pointers it recreates are safe to dereference or not hinges entirely on whether the pointer
to data used to recreate the full pointer is safe to dereference.

#   Example.

A simple example showing how to take apart a pointer and recreate it.

```
use rfc2580::{from_raw_parts, into_raw_parts};

let array = [1; 4];
let slice = &array[..];
let (meta, data) = into_raw_parts(slice as *const [i32]);
let reconstituted = from_raw_parts(meta, data);
assert_eq!(slice as *const [i32], reconstituted);
```
