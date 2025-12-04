//! A simple flat set backed by a sorted `Vec<T>`.
//!
//! Provides a minimal subset of `BTreeSet` functionality used by this crate:
//! - `new()` constructor
//! - `insert(T)` which keeps elements sorted and unique
//! - `iter()` over `&T` in sorted order
//! - `get()` lookup by value using binary search
//!
//! This is intentionally small and tailored for our internal use.

use core::fmt;

#[derive(Clone)]
pub struct FlatSet<T> {
    elems: Vec<T>,
}

impl<T> Default for FlatSet<T> {
    fn default() -> Self {
        Self { elems: Vec::new() }
    }
}

impl<T: Ord> FlatSet<T> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize { self.elems.len() }
    pub fn is_empty(&self) -> bool { self.elems.is_empty() }

    pub fn insert(&mut self, value: T) -> bool {
        match self.elems.binary_search(&value) {
            Ok(_) => false,
            Err(idx) => {
                self.elems.insert(idx, value);
                true
            }
        }
    }

    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.elems.iter()
    }

    /// Find an element equal to `value` using binary search.
    ///
    /// Supports nested borrowing (e.g., `T = Box<Node>`, `value: &str`) as long as
    /// there exists a chain `T: Borrow<B>` and `B: Borrow<Q>` with `Q: Ord`.
    pub fn get<'a, Q, B>(&'a self, value: &Q) -> Option<&'a T>
    where
        T: core::borrow::Borrow<B>,
        B: core::borrow::Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self
            .elems
            .binary_search_by(|e| e.borrow().borrow().cmp(value))
        {
            Ok(idx) => Some(&self.elems[idx]),
            Err(_) => None,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for FlatSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.elems.iter()).finish()
    }
}
