#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::option_if_let_else)]
#![allow(unknown_lints)]
#![warn(missing_docs)]
#![warn(missing_debug_implementations)]
#![warn(missing_copy_implementations)]
#![warn(rust_2018_idioms)]
#![warn(rust_2021_compatibility)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unsafe_op_in_unsafe_fn)]
#![warn(unused_qualifications)]
#![warn(variant_size_differences)]
// Enable feature callouts in generated documentation:
// https://doc.rust-lang.org/beta/unstable-book/language-features/doc-cfg.html
//
// This approach is borrowed from tokio.
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, feature(doc_alias))]

//! A wrapper around the decomposed parts of a `Vec<T>`.
//!
//! This crate defines a struct that contains the `Vec`'s internal pointer,
//! length, and allocated capacity.
//!
//! [`RawParts`] makes [`Vec::from_raw_parts`] and [`Vec::into_raw_parts`] easier
//! to use by giving names to the returned values. This prevents errors from
//! mixing up the two `usize` values of length and capacity.
//!
//! # Examples
//!
//! ```
//! use raw_parts::RawParts;
//!
//! let v: Vec<i32> = vec![-1, 0, 1];
//!
//! let RawParts { ptr, length, capacity } = RawParts::from_vec(v);
//!
//! let rebuilt = unsafe {
//!     // We can now make changes to the components, such as
//!     // transmuting the raw pointer to a compatible type.
//!     let ptr = ptr as *mut u32;
//!     let raw_parts = RawParts { ptr, length, capacity };
//!
//!     RawParts::into_vec(raw_parts)
//! };
//! assert_eq!(rebuilt, [4294967295, 0, 1]);
//! ```
//!
//! # `no_std`
//!
//! raw-parts is `no_std` compatible with a required dependency on [`alloc`].

#![no_std]
#![doc(html_root_url = "https://docs.rs/raw-parts/1.1.2")]

extern crate alloc;

use alloc::vec::Vec;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::mem::ManuallyDrop;

/// A wrapper around the decomposed parts of a `Vec<T>`.
///
/// This struct contains the `Vec`'s internal pointer, length, and allocated
/// capacity.
///
/// `RawParts` makes [`Vec::from_raw_parts`] and [`Vec::into_raw_parts`] easier
/// to use by giving names to the returned values. This prevents errors from
/// mixing up the two `usize` values of length and capacity.
///
/// # Examples
///
/// ```
/// use raw_parts::RawParts;
///
/// let v: Vec<i32> = vec![-1, 0, 1];
///
/// let RawParts { ptr, length, capacity } = RawParts::from_vec(v);
///
/// let rebuilt = unsafe {
///     // We can now make changes to the components, such as
///     // transmuting the raw pointer to a compatible type.
///     let ptr = ptr as *mut u32;
///     let raw_parts = RawParts { ptr, length, capacity };
///
///     RawParts::into_vec(raw_parts)
/// };
/// assert_eq!(rebuilt, [4294967295, 0, 1]);
/// ```
pub struct RawParts<T> {
    /// A non-null pointer to a buffer of `T`.
    ///
    /// This pointer is the same as the value returned by [`Vec::as_mut_ptr`] in
    /// the source vector.
    pub ptr: *mut T,
    /// The number of elements in the source vector, also referred to as its
    /// "length".
    ///
    /// This value is the same as the value returned by [`Vec::len`] in the
    /// source vector.
    pub length: usize,
    /// The number of elements the source vector can hold without reallocating.
    ///
    /// This value is the same as the value returned by [`Vec::capacity`] in the
    /// source vector.
    pub capacity: usize,
}

impl<T> From<Vec<T>> for RawParts<T> {
    /// Decompose a `Vec<T>` into its raw components.
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

impl<T> fmt::Debug for RawParts<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("RawParts")
            .field("ptr", &self.ptr)
            .field("length", &self.length)
            .field("capacity", &self.capacity)
            .finish()
    }
}

impl<T> PartialEq for RawParts<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr && self.length == other.length && self.capacity == other.capacity
    }
}

impl<T> Eq for RawParts<T> {}

impl<T> Hash for RawParts<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ptr.hash(state);
        self.length.hash(state);
        self.capacity.hash(state);
    }
}

// Do not implement the `From` trait in the other direction since `crate::from`
// is an unsafe function.
//
// ```
// impl<T> From<RawParts<T>> for Vec<T> {
//     fn from(raw_parts: RawParts<T>) -> Self {
//         // ERROR: this requires `unsafe`, which we don't want to hide in a
//         // `From` impl.
//         from(raw_parts)
//     }
// }

impl<T> RawParts<T> {
    /// Construct the raw components of a `Vec<T>` by decomposing it.
    ///
    /// Returns a struct containing the raw pointer to the underlying data, the
    /// length of the vector (in elements), and the allocated capacity of the
    /// data (in elements).
    ///
    /// After calling this function, the caller is responsible for the memory
    /// previously managed by the `Vec`. The only way to do this is to convert
    /// the raw pointer, length, and capacity back into a `Vec` with the
    /// [`Vec::from_raw_parts`] function or the [`into_vec`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`into_vec`]: Self::into_vec
    ///
    /// # Examples
    ///
    /// ```
    /// use raw_parts::RawParts;
    ///
    /// let v: Vec<i32> = vec![-1, 0, 1];
    ///
    /// let RawParts { ptr, length, capacity } = RawParts::from_vec(v);
    ///
    /// let rebuilt = unsafe {
    ///     // We can now make changes to the components, such as
    ///     // transmuting the raw pointer to a compatible type.
    ///     let ptr = ptr as *mut u32;
    ///     let raw_parts = RawParts { ptr, length, capacity };
    ///
    ///     RawParts::into_vec(raw_parts)
    /// };
    /// assert_eq!(rebuilt, [4294967295, 0, 1]);
    /// ```
    #[must_use]
    pub fn from_vec(vec: Vec<T>) -> Self {
        // TODO: convert to `Vec::into_raw_parts` once it is stabilized.
        // See: https://doc.rust-lang.org/1.56.0/src/alloc/vec/mod.rs.html#717-720
        //
        // https://github.com/rust-lang/rust/issues/65816
        let mut me = ManuallyDrop::new(vec);
        let (ptr, length, capacity) = (me.as_mut_ptr(), me.len(), me.capacity());

        Self {
            ptr,
            length,
            capacity,
        }
    }

    /// Creates a `Vec<T>` directly from the raw components of another vector.
    ///
    /// This function is declared as an associated function and must be called
    /// as `RawParts::into_vec(raw_parts)`.
    ///
    /// # Safety
    ///
    /// This function has the same safety invariants as [`Vec::from_raw_parts`],
    /// which are repeated in the following paragraphs.
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * `ptr` needs to have been previously allocated via [`String`]/`Vec<T>`
    ///   (at least, it's highly likely to be incorrect if it wasn't).
    /// * `T` needs to have the same size and alignment as what `ptr` was allocated with.
    ///   (`T` having a less strict alignment is not sufficient, the alignment really
    ///   needs to be equal to satisfy the [`dealloc`] requirement that memory must be
    ///   allocated and deallocated with the same layout.)
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the capacity that the pointer was allocated with.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures. For example it is **not** safe
    /// to build a `Vec<u8>` from a pointer to a C `char` array with length `size_t`.
    /// It's also not safe to build one from a `Vec<u16>` and its length, because
    /// the allocator cares about the alignment, and these two types have different
    /// alignments. The buffer was allocated with alignment 2 (for `u16`), but after
    /// turning it into a `Vec<u8>` it'll be deallocated with alignment 1.
    ///
    /// The ownership of `ptr` is effectively transferred to the
    /// `Vec<T>` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// [`String`]: alloc::string::String
    /// [`dealloc`]: alloc::alloc::GlobalAlloc::dealloc
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ptr;
    /// use core::mem;
    ///
    /// use raw_parts::RawParts;
    ///
    /// let v = vec![1, 2, 3];
    ///
    /// // Pull out the various important pieces of information about `v`
    /// let RawParts { ptr, length, capacity } = RawParts::from_vec(v);
    ///
    /// unsafe {
    ///     // Overwrite memory with 4, 5, 6
    ///     for i in 0..length as isize {
    ///         ptr::write(ptr.offset(i), 4 + i);
    ///     }
    ///
    ///     // Put everything back together into a Vec
    ///     let raw_parts = RawParts { ptr, length, capacity };
    ///     let rebuilt = RawParts::into_vec(raw_parts);
    ///     assert_eq!(rebuilt, [4, 5, 6]);
    /// }
    /// ```
    #[must_use]
    #[allow(clippy::needless_pass_by_value)]
    pub unsafe fn into_vec(this: Self) -> Vec<T> {
        let Self {
            ptr,
            length,
            capacity,
        } = this;

        // Safety:
        //
        // The safety invariants that callers must uphold when calling `from` match
        // the safety invariants of `Vec::from_raw_parts`.
        unsafe { Vec::from_raw_parts(ptr, length, capacity) }
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;
    use alloc::vec::Vec;
    use core::hash::{Hash, Hasher};

    use rustc_hash::FxHasher;

    use crate::RawParts;

    #[test]
    fn roundtrip() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9

        let raw_parts = RawParts::from_vec(vec);
        let raw_ptr = raw_parts.ptr;

        let mut roundtripped_vec = unsafe { RawParts::into_vec(raw_parts) };

        assert_eq!(roundtripped_vec.capacity(), 100);
        assert_eq!(roundtripped_vec.len(), 9);
        assert_eq!(roundtripped_vec.as_mut_ptr(), raw_ptr);
    }

    #[test]
    fn from_vec_sets_ptr() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9
        let ptr = vec.as_mut_ptr();

        let raw_parts = RawParts::from_vec(vec);
        assert_eq!(raw_parts.ptr, ptr);
    }

    #[test]
    fn from_vec_sets_length() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9

        let raw_parts = RawParts::from_vec(vec);
        assert_eq!(raw_parts.length, 9);
    }

    #[test]
    fn from_vec_sets_capacity() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9

        let raw_parts = RawParts::from_vec(vec);
        assert_eq!(raw_parts.capacity, 100);
    }

    #[test]
    fn from_sets_ptr() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9
        let ptr = vec.as_mut_ptr();

        let raw_parts = RawParts::from(vec);
        assert_eq!(raw_parts.ptr, ptr);
    }

    #[test]
    fn from_sets_length() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9

        let raw_parts = RawParts::from(vec);
        assert_eq!(raw_parts.length, 9);
    }

    #[test]
    fn from_sets_capacity() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9

        let raw_parts = RawParts::from(vec);
        assert_eq!(raw_parts.capacity, 100);
    }

    #[test]
    fn debug_test() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9
        let raw_parts = RawParts::from_vec(vec);

        assert_eq!(
            format!(
                "RawParts {{ ptr: {:?}, length: 9, capacity: 100 }}",
                raw_parts.ptr
            ),
            format!("{:?}", raw_parts)
        );
    }

    #[test]
    fn partial_eq_fail_pointer() {
        let mut vec_1 = Vec::with_capacity(100); // capacity is 100
        vec_1.extend_from_slice(b"123456789"); // length is 9
        let mut vec_2 = Vec::with_capacity(100); // capacity is 100
        vec_2.extend_from_slice(b"123456789"); // length is 9

        let raw_parts_1 = RawParts::from_vec(vec_1);
        let raw_parts_2 = RawParts::from_vec(vec_2);
        assert_ne!(raw_parts_1, raw_parts_2);
    }

    #[test]
    fn partial_eq_fail_capacity() {
        let mut vec_1 = Vec::with_capacity(100); // capacity is 100
        vec_1.extend_from_slice(b"123456789"); // length is 9
        let mut vec_2 = Vec::with_capacity(101); // capacity is 101
        vec_2.extend_from_slice(b"123456789"); // length is 9

        let raw_parts_1 = RawParts::from_vec(vec_1);
        let raw_parts_2 = RawParts::from_vec(vec_2);
        assert_ne!(raw_parts_1, raw_parts_2);
    }

    #[test]
    fn partial_eq_fail_length() {
        let mut vec_1 = Vec::with_capacity(100); // capacity is 100
        vec_1.extend_from_slice(b"123456789"); // length is 9
        let mut vec_2 = Vec::with_capacity(100); // capacity is 100
        vec_2.extend_from_slice(b"12345678"); // length is 8

        let raw_parts_1 = RawParts::from_vec(vec_1);
        let raw_parts_2 = RawParts::from_vec(vec_2);
        assert_ne!(raw_parts_1, raw_parts_2);
    }

    #[test]
    fn partial_eq_pass() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9

        let RawParts {
            ptr,
            length,
            capacity,
        } = RawParts::from_vec(vec);
        let a = RawParts {
            ptr,
            length,
            capacity,
        };
        let b = RawParts {
            ptr,
            length,
            capacity,
        };
        assert_eq!(a, b);
    }

    #[test]
    fn hash_fail_pointer() {
        let mut vec_1 = Vec::with_capacity(100); // capacity is 100
        vec_1.extend_from_slice(b"123456789"); // length is 9
        let mut vec_2 = Vec::with_capacity(100); // capacity is 100
        vec_2.extend_from_slice(b"123456789"); // length is 9

        let raw_parts_1 = RawParts::from_vec(vec_1);
        let mut hasher = FxHasher::default();
        raw_parts_1.hash(&mut hasher);
        let hash_a = hasher.finish();

        let raw_parts_2 = RawParts::from_vec(vec_2);
        let mut hasher = FxHasher::default();
        raw_parts_2.hash(&mut hasher);
        let hash_b = hasher.finish();

        assert_ne!(hash_a, hash_b);
    }

    #[test]
    fn hash_fail_capacity() {
        let mut vec_1 = Vec::with_capacity(100); // capacity is 100
        vec_1.extend_from_slice(b"123456789"); // length is 9
        let mut vec_2 = Vec::with_capacity(101); // capacity is 101
        vec_2.extend_from_slice(b"123456789"); // length is 9

        let raw_parts_1 = RawParts::from_vec(vec_1);
        let mut hasher = FxHasher::default();
        raw_parts_1.hash(&mut hasher);
        let hash_a = hasher.finish();

        let raw_parts_2 = RawParts::from_vec(vec_2);
        let mut hasher = FxHasher::default();
        raw_parts_2.hash(&mut hasher);
        let hash_b = hasher.finish();

        assert_ne!(hash_a, hash_b);
    }

    #[test]
    fn hash_fail_length() {
        let mut vec_1 = Vec::with_capacity(100); // capacity is 100
        vec_1.extend_from_slice(b"123456789"); // length is 9
        let mut vec_2 = Vec::with_capacity(100); // capacity is 100
        vec_2.extend_from_slice(b"12345678"); // length is 8

        let raw_parts_1 = RawParts::from_vec(vec_1);
        let mut hasher = FxHasher::default();
        raw_parts_1.hash(&mut hasher);
        let hash_a = hasher.finish();

        let raw_parts_2 = RawParts::from_vec(vec_2);
        let mut hasher = FxHasher::default();
        raw_parts_2.hash(&mut hasher);
        let hash_b = hasher.finish();

        assert_ne!(hash_a, hash_b);
    }

    #[test]
    fn hash_eq_pass() {
        let mut vec = Vec::with_capacity(100); // capacity is 100
        vec.extend_from_slice(b"123456789"); // length is 9
        let raw_parts = RawParts::from_vec(vec);

        let mut hasher = FxHasher::default();
        raw_parts.hash(&mut hasher);
        let hash_a = hasher.finish();

        let mut hasher = FxHasher::default();
        raw_parts.hash(&mut hasher);
        let hash_b = hasher.finish();

        assert_eq!(hash_a, hash_b);
    }
}

// Ensure code blocks in `README.md` compile.
//
// This module declaration should be kept at the end of the file, in order to
// not interfere with code coverage.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
mod readme {}
