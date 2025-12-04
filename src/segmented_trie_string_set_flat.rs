use crate::flat_set::FlatSet;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;

// Container abstraction to allow selecting the children set as a generic parameter
// while keeping efficient, static dispatch and zero-cost iteration.
pub trait ChildrenOps<T: Ord> {
    type Iter<'a>: Iterator<Item = &'a T>
    where
        Self: 'a,
        T: 'a;

    fn new() -> Self
    where
        Self: Sized;
    fn insert(&mut self, value: T) -> bool;
    fn iter(&self) -> Self::Iter<'_>;
    fn is_empty(&self) -> bool;
}

pub trait ChildrenFamily {
    type Set<T: Ord>: ChildrenOps<T>;
}

pub struct FlatFamily;
pub struct BTreeFamily;

// Implement ChildrenOps<T> for containers storing Box<T>, exposing &T during iteration
// FlatSet<Box<T>>
pub struct FlatIter<'a, T> { it: core::slice::Iter<'a, Box<T>> }
impl<'a, T> Iterator for FlatIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> { self.it.next().map(|b| &**b) }
}

impl<T: Ord> ChildrenOps<T> for FlatSet<Box<T>> {
    type Iter<'a> = FlatIter<'a, T> where Self: 'a, T: 'a;

    fn new() -> Self where Self: Sized { FlatSet::new() }

    fn insert(&mut self, value: T) -> bool {
        FlatSet::insert(self, Box::new(value))
    }

    fn iter(&self) -> Self::Iter<'_> { FlatIter { it: FlatSet::iter(self) } }
    fn is_empty(&self) -> bool { FlatSet::is_empty(self) }
}

// BTreeSet<Box<T>>
pub struct BTreeIter<'a, T> { it: std::collections::btree_set::Iter<'a, Box<T>> }
impl<'a, T> Iterator for BTreeIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> { self.it.next().map(|b| &**b) }
}

impl<T: Ord> ChildrenOps<T> for BTreeSet<Box<T>> {
    type Iter<'a> = BTreeIter<'a, T> where Self: 'a, T: 'a;

    fn new() -> Self where Self: Sized { BTreeSet::new() }
    fn insert(&mut self, value: T) -> bool { BTreeSet::insert(self, Box::new(value)) }
    fn iter(&self) -> Self::Iter<'_> { BTreeIter { it: BTreeSet::iter(self) } }
    fn is_empty(&self) -> bool { BTreeSet::is_empty(self) }
}

impl ChildrenFamily for FlatFamily {
    type Set<T: Ord> = FlatSet<Box<T>>;
}

impl ChildrenFamily for BTreeFamily {
    type Set<T: Ord> = BTreeSet<Box<T>>;
}

impl<T: Ord> ChildrenOps<T> for FlatSet<T> {
    type Iter<'a> = core::slice::Iter<'a, T> where Self: 'a, T: 'a;

    fn new() -> Self { FlatSet::new() }
    fn insert(&mut self, value: T) -> bool { FlatSet::insert(self, value) }
    fn iter(&self) -> Self::Iter<'_> { FlatSet::iter(self) }
    fn is_empty(&self) -> bool { FlatSet::is_empty(self) }
}

impl<T: Ord> ChildrenOps<T> for BTreeSet<T> {
    type Iter<'a> = std::collections::btree_set::Iter<'a, T> where Self: 'a, T: 'a;

    fn new() -> Self { BTreeSet::new() }
    fn insert(&mut self, value: T) -> bool { BTreeSet::insert(self, value) }
    fn iter(&self) -> Self::Iter<'_> { BTreeSet::iter(self) }
    fn is_empty(&self) -> bool { BTreeSet::is_empty(self) }
}

// Optimized lookup for children by segment key without linear scans.
// Implemented for actual set types we use to store nodes (boxed internally).
// Kept private to avoid leaking the private `Node<F>` type via public APIs.
trait ChildrenLookup<F: ChildrenFamily> {
    fn get_child_ptr(&self, key: &str) -> Option<*const Node<F>>;
}

// FlatSet<Box<Node<F>>> internally. Binary search by borrowed str via FlatSet::get
impl<F: ChildrenFamily> ChildrenLookup<F> for FlatSet<Box<Node<F>>> {
    fn get_child_ptr(&self, key: &str) -> Option<*const Node<F>> {
        crate::flat_set::FlatSet::get::<str, Node<F>>(self, key).map(|b| b.as_ref() as *const _)
    }
}

impl<F: ChildrenFamily> ChildrenLookup<F> for BTreeSet<Box<Node<F>>> {
    fn get_child_ptr(&self, key: &str) -> Option<*const Node<F>> {
        // Create a lightweight probe node that compares only by `key` and borrow it
        let probe = Node::<F>::probe_for_key(key);
        std::collections::BTreeSet::get(self, &probe).map(|b| &**b as *const _)
    }
}

// Choose the default family via feature flag to preserve existing behavior, but both
// families are always available for explicit instantiation (e.g., in benches).
// Default families use boxed storage to guarantee stable addresses for nodes
#[cfg(feature = "btreeset_children")]
pub type DefaultFamily = BTreeFamily;
#[cfg(not(feature = "btreeset_children"))]
pub type DefaultFamily = FlatFamily;

#[derive(Debug, PartialEq)]
pub struct NodeId {
    pub value: usize, // pointer address exposed as usize
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsertError {
    InvalidArg,
    KeyAlreadyInserted,
}

#[derive(Debug)]
pub struct SegmentedTrieSet<const DELIMITER: char, F: ChildrenFamily = DefaultFamily> {
    root: Box<Node<F>>,
}

impl<const DELIMITER: char, F: ChildrenFamily> Default for SegmentedTrieSet<DELIMITER, F> {
    fn default() -> Self {
        Self { root: Box::new(Node::new_root()) }
    }
}

impl<const DELIMITER: char, F: ChildrenFamily> SegmentedTrieSet<DELIMITER, F> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> Iter<DELIMITER, F> { Iter::from_first_leaf(&*self.root) }

    pub unsafe fn find_by_id(&self, id: NodeId) -> Option<Iter<DELIMITER, F>> {
        if id.value != 0 { Some(Iter::from_ptr(id.value as *const Node<F>)) } else { None }
    }
}

// Constrained inherent impl: these methods are only available when the children set
// supports efficient lookup by segment key via our private ChildrenLookup.
#[allow(private_bounds)]
impl<const DELIMITER: char, F: ChildrenFamily> SegmentedTrieSet<DELIMITER, F>
where
    <F as ChildrenFamily>::Set<Node<F>>: ChildrenLookup<F>,
{
    /// Returns an iterator positioned at the leaf that exactly matches `key`,
    /// or `None` if the key is not present.
    pub fn get(&self, key: &str) -> Option<Iter<DELIMITER, F>> {
        // Traverse from root by segments using iterator combinators
        let root_ptr: *const Node<F> = &*self.root;
        let cur_opt = key
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .fold(Some(root_ptr), |acc, seg| acc.and_then(|cur| Node::find_child_ptr(cur, seg)));

        cur_opt.and_then(|cur| unsafe { if (*cur).is_leaf { Some(Iter::from_ptr(cur)) } else { None } })
    }

    pub fn equal_range(&self, prefix: &str) -> (Iter<DELIMITER, F>, Iter<DELIMITER, F>) {
        let root_ptr: *const Node<F> = &*self.root;
        let cur_opt = prefix
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .fold(Some(root_ptr), |acc, seg| acc.and_then(|cur| Node::find_child_ptr(cur, seg)));

        if let Some(cur) = cur_opt {
            if let Some(n) = Node::descend(cur) {
                let begin = Iter::from_ptr(n);
                let end = Node
                    ::first_leaf_of_next_sibling(cur)
                    .map(|next| Iter::from_ptr(next))
                    .unwrap_or_else(|| Iter::new());
                (begin, end)
            } else {
                (Iter::new(), Iter::new())
            }
        } else {
            (Iter::new(), Iter::new())
        }
    }

    pub fn insert(&mut self, key: &str) -> Result<NodeId, InsertError> {
        if key.is_empty() || key.split(DELIMITER).any(|s| s.is_empty()) {
            return Err(InsertError::InvalidArg);
        }

        let cur_ptr: *mut Node<F> = key
            .split(DELIMITER)
            .filter(|seg| !seg.is_empty())
            .fold(&mut *self.root as *mut Node<F>, |cur_ptr, seg| {
                if let Some(next_ptr) = Node::find_child_ptr(cur_ptr as *const _, seg) {
                    next_ptr as *mut _
                } else {
                    Node::insert_child(cur_ptr, seg) as *mut _
                }
        });

        unsafe {
            if (*cur_ptr).is_leaf {
                return Err(InsertError::KeyAlreadyInserted);
            }
            (*cur_ptr).is_leaf = true;
            Ok(NodeId { value: cur_ptr as usize })
        }
    }

    pub fn contains(&self, key: &str) -> bool {
        self.get(key).is_some()
    }
}

// --- Internal pointer-based Node ---

struct Node<F: ChildrenFamily> {
    parent: Option<*const Node<F>>,
    key: String, // segment at this node (empty for root)
    children: <F as ChildrenFamily>::Set<Node<F>>,
    is_leaf: bool,
}

impl<F: ChildrenFamily> fmt::Debug for Node<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("key", &self.key)
            .field("is_leaf", &self.is_leaf)
            .finish()
    }
}

impl<F: ChildrenFamily> PartialEq for Node<F> { fn eq(&self, other: &Self) -> bool { self.key == other.key } }
impl<F: ChildrenFamily> Eq for Node<F> {}
impl<F: ChildrenFamily> PartialOrd for Node<F> { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
impl<F: ChildrenFamily> Ord for Node<F> { fn cmp(&self, other: &Self) -> Ordering { self.key.cmp(&other.key) } }

impl<F: ChildrenFamily> core::borrow::Borrow<str> for Node<F> {
    fn borrow(&self) -> &str { &self.key }
}

impl<F: ChildrenFamily> Node<F> {
    fn new_root() -> Self {
        Self { parent: None, key: String::new(), children: <F as ChildrenFamily>::Set::<Node<F>>::new(), is_leaf: false }
    }
    fn new_with_parent(parent: *const Node<F>, key: &str) -> Self {
        Self { parent: Some(parent), key: key.to_string(), children: <F as ChildrenFamily>::Set::<Node<F>>::new(), is_leaf: false }
    }
    #[inline]
    fn probe_for_key(key: &str) -> Self {
        Self { parent: None, key: key.to_string(), children: <F as ChildrenFamily>::Set::<Node<F>>::new(), is_leaf: false }
    }

    // ---- Helpers that operate on nodes (moved back from SegmentedTrieSet) ----
    #[inline]
    fn children_iter<'a>(node: *const Node<F>) -> impl Iterator<Item = &'a Node<F>>
    where
        F: 'a,
        <F as ChildrenFamily>::Set<Node<F>>: 'a,
    {
        unsafe { (&*node).children.iter() }
    }

    #[inline]
    fn find_child_ptr(parent: *const Node<F>, seg: &str) -> Option<*const Node<F>>
    where
        <F as ChildrenFamily>::Set<Node<F>>: ChildrenLookup<F>,
    {
        if seg.is_empty() { return Some(parent); }
        unsafe { (&*parent).children.get_child_ptr(seg) }
    }

    #[inline]
    fn insert_child(parent: *mut Node<F>, seg: &str) -> *const Node<F> {
        let parent_const = parent as *const Node<F>;
        let new_child = Node::new_with_parent(parent_const, seg);
        let inserted = unsafe { ChildrenOps::insert(&mut (*parent).children, new_child) };
        debug_assert!(inserted, "duplicate child inserted unexpectedly");
        // Find the pointer we just inserted by scanning this parent's children
        unsafe {
            (&*parent)
                .children
                .iter()
                .find_map(|ch| if ch.key == seg { Some(ch as *const _) } else { None })
                .expect("inserted child not found")
        }
    }

    fn descend(start: *const Node<F>) -> Option<*const Node<F>> {
        unsafe {
            let node = &*start;
            if node.is_leaf { return Some(start); }
            Node::children_iter(start)
                .find_map(|ch| Node::descend(ch as *const _))
        }
    }

    fn first_leaf_of_next_sibling(cur: *const Node<F>) -> Option<*const Node<F>> {
        let parent_ptr = unsafe { (&*cur).parent? };
        Node::children_iter(parent_ptr)
            .zip(Node::children_iter(parent_ptr).skip(1))
            .find_map(|(a, b)| {
                if (a as *const _) == cur { Node::descend(b as *const _) } else { None }
            })
    }

    fn increment(cur: *const Node<F>) -> Option<*const Node<F>> {
        // If has children, go to first leaf of first child
        Node::children_iter(cur)
            .next()
            .and_then(|first_child| Node::descend(first_child as *const _))
            .or_else(|| {
                // Otherwise, walk up to find next sibling subtree
                std::iter::successors(Some(cur), |&n| unsafe { (&*n).parent })
                    .find_map(|n| Node::first_leaf_of_next_sibling(n))
            })
    }
}

impl<const D: char, F: ChildrenFamily> SegmentedTrieSet<D, F> {}


// --- Public iterators ---
pub struct Iter<const D: char, F: ChildrenFamily> {
    node: Option<*const Node<F>>,
}

impl<const D: char, F: ChildrenFamily> Iter<D, F> {
    pub fn new() -> Self {
        Self { node: None }
    }

    pub fn id(&self) -> NodeId { NodeId { value: self.node.map(|p| p as usize).unwrap_or(0) } }

    fn from_ptr(ptr: *const Node<F>) -> Self { Self { node: Some(ptr) } }

    fn from_first_leaf(node: *const Node<F>) -> Self {
        if let Some(ptr) = Node::descend(node) { Self { node: Some(ptr) } } else { Self::new() }
    }

    fn key(&self) -> Option<String> {
        let node = self.node?;
        // Reconstruct by walking parents using iterator combinators
        let mut parts: Vec<&str> = std::iter::successors(Some(node), |&p| unsafe { (&*p).parent })
            .map(|p| unsafe { (&*p).key.as_str() })
            .filter(|s| !s.is_empty())
            .collect();
        parts.reverse();
        Some(parts.join(&D.to_string()))
    }
}

impl<const D: char, F: ChildrenFamily> fmt::Debug for Iter<D, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(k) = self.key() {
            write!(f, "Iter({k})")
        } else {
            write!(f, "Iter(end)")
        }

    }
}

impl<const D: char, F: ChildrenFamily> PartialEq for Iter<D, F> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl<const D: char, F: ChildrenFamily> Eq for Iter<D, F> {}

impl<const D: char, F: ChildrenFamily> Iterator for Iter<D, F> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.node.is_none() {
            return None;
        }
        let key = self.key();
        self.node = Node::increment(self.node.unwrap());
        key
    }
}

impl<const DELIMITER: char, F: ChildrenFamily> IntoIterator for &SegmentedTrieSet<DELIMITER, F> {
    type Item = String;
    type IntoIter = Iter<DELIMITER, F>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_find_contains_basic() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id_a = trie.insert("a").unwrap();
        let id_ab = trie.insert("a/b").unwrap();
        assert!(trie.contains("a"));
        assert!(trie.contains("a/b"));
        assert!(!trie.contains("b"));
        assert_ne!(id_a.value, 0);
        assert_ne!(id_ab.value, 0);
    }

    #[test]
    fn iterator_order_and_keys() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let _ = trie.insert("a/b");
        let _ = trie.insert("a/c");
        let _ = trie.insert("b");
        let _ = trie.insert("a");

        let keys: Vec<String> = trie.iter().collect();

        assert_eq!(keys, vec!["a".to_string(), "a/b".to_string(), "a/c".to_string(), "b".to_string()]);
    }

    #[test]
    fn equal_range_prefix_collects_expected() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let _ = trie.insert("a/b/1");
        let _ = trie.insert("a/b/2");
        let _ = trie.insert("a/c/1");
        let _ = trie.insert("a/c/2");
        let _ = trie.insert("z");

        let (mut begin, end) = trie.equal_range("a/b");
        let mut seen: Vec<String> = Vec::new();
        while begin != end {
            if let Some(k) = begin.next() { seen.push(k); } else { break; }
        }

        assert_eq!(seen, vec!["a/b/1".to_string(), "a/b/2".to_string()]);
    }

    #[test]
    fn find_by_id() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id1 = trie.insert("x/y").unwrap();
        let id2 = trie.insert("x/z").unwrap();
        let id3 = trie.insert("x/x").unwrap();
        // valid id
        unsafe {
            let it1 = trie.find_by_id(id1).expect("should find by id");
            assert_eq!(it1.key().unwrap(), "x/y".to_string());
            let it2 = trie.find_by_id(id2).expect("should find by id");
            assert_eq!(it2.key().unwrap(), "x/z".to_string());
            let it3 = trie.find_by_id(id3).expect("should find by id");
            assert_eq!(it3.key().unwrap(), "x/x".to_string());
        }
        unsafe {
            assert!(trie.find_by_id(NodeId { value: 0 }).is_none());
        }
    }

    #[test]
    fn insert_rejects_empty_segments() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        assert_eq!(trie.insert("/a"), Err(InsertError::InvalidArg));
        assert_eq!(trie.insert("a//b"), Err(InsertError::InvalidArg));
        assert_eq!(trie.insert("trail/"), Err(InsertError::InvalidArg));
        assert_eq!(trie.insert("").err(), Some(InsertError::InvalidArg));
    }

    #[test]
    fn insert_same_key_twice_errors() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        assert!(trie.insert("a/b").is_ok());
        assert_eq!(trie.insert("a/b"), Err(InsertError::KeyAlreadyInserted));
    }
}