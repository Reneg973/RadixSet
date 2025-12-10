#[cfg(feature = "flat_map_children")]
use litemap::LiteMap;
#[cfg(feature = "flat_map_children")]
use litemap::store::Store;
#[cfg(feature = "flat_map_children")]
use litemap::store::StoreMut;

use std::ops::Deref;
use std::borrow::Borrow;
use std::cmp::Ordering;
#[cfg(not(feature = "flat_map_children"))]
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt;
use std::ptr::NonNull;

///////////////////////////////////////////////////////////////////////
// pub types

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct NodeId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidArg,
    AlreadyExists,
    NotFound,
}

pub struct SegmentedTrieSet<const DELIMITER: char> {
    segments: StringPool,
    root: Box<Node>, // ensure this is dropped first
}

// --- Public iterators ---
pub struct Iter<'r, const D: char> {
    node: Option<&'r Node>,
}

// pub types
///////////////////////////////////////////////////////////////////////
// implementations

impl<const DELIMITER: char> Default for SegmentedTrieSet<DELIMITER> {
    fn default() -> Self {
        Self {
            root: Box::new(Node::default()),
            segments: StringPool::new(),
        }
    }
}

impl<const DELIMITER: char> SegmentedTrieSet<DELIMITER> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> Iter<'_, DELIMITER> {
        Iter::from_first_leaf(self.root.as_ref())
    }

    pub fn contains(&self, key: &str) -> bool {
        self.get(key).is_ok()
    }

    pub fn get(&self, key: &str) -> Result<Iter<'_, DELIMITER>, Error> {
        self.find_node(key)
          .and_then(|cur| if cur.is_leaf {
              Ok(Iter::from(cur))
          } else {
              Err(Error::NotFound)
          })
    }

    pub fn get_by_id(&self, id: NodeId) -> Option<Iter<'_, DELIMITER>> {
        unsafe { Node::from(id).map(|p| Iter::from(p.as_ref())) }
    }

    pub fn insert(&mut self, key: &str) -> Result<NodeId, Error> {
        if key.split(DELIMITER)
          .any(|s| s.is_empty()) {
            return Err(Error::InvalidArg);
        }

        let leaf = key
            .split(DELIMITER)
            .fold(self.root.as_mut(), |cur_node, seg| {
                let seg =  self.segments.get_or_insert(seg);
                let parent = NonNull::from_ref(cur_node);
                cur_node.children.entry(Key(NonNull::from(seg)))
                    .or_insert_with_key(|k| {
                        // allocate segment string in arena as a nonmoving String we can reference on
                        Box::new(Node::new_child(parent, k))
                    })
        });

        if !leaf.is_leaf {
            leaf.is_leaf = true;
            return Ok(leaf.id());
        }
        Err(Error::AlreadyExists)
    }

    pub fn range(&self, prefix: &str) -> RangeIter<'_, DELIMITER> {
        let parent = match self.find_node(prefix) {
            Ok(node) => node,
            Err(_) => return RangeIter::new(Iter::new(), Iter::new()),
        };
        // find the first leaf under this node
        parent.first_leaf()
          .map(|n| {
              let end = match parent.first_leaf_of_next_sibling() {
                  Some(node) => Iter::from(node),
                  None => Iter::new(),
              };
              RangeIter::new(Iter::from(n), end)
          })
          .unwrap_or_else(|| return RangeIter::new(Iter::new(), Iter::new()))
    }

    fn find_node(&self, prefix: &str) -> Result<&Node, Error> {
        prefix
          .split(DELIMITER)
          .try_fold(self.root.as_ref(), |acc, seg| {
              acc.children.get(seg)
                .map(|b| b.as_ref())
                .ok_or(if seg.is_empty() { Error::InvalidArg } else { Error::NotFound })
          })
    }
}

// implementations
///////////////////////////////////////////////////////////////////////
// privates

// --- Internal pointer-based Node ---

// static empty key used for the root node
struct Node {
    parent: Option<NonNull<Node>>,
    key: Key, // pointer into arena (or static empty for root)
    children: Children<Key, Box<Node>>,
    is_leaf: bool,
}

impl Default for Node {
    fn default() -> Self {
        Self {
            parent: None,
            key: Key::from_ref(""),
            children: Self::children_new(),
            is_leaf: false,
        }
    }
}
impl Node {
    // cfg-driven constructor for the concrete map
    #[cfg(feature = "flat_map_children")]
    fn children_new<K: Ord, V>() -> Children<K, V> { LiteMap::new() }
    #[cfg(not(feature = "flat_map_children"))]
    fn children_new<K: Ord, V>() -> Children<K, V> { BTreeMap::new() }

    fn new_child(parent: NonNull<Node>, key: &Key) -> Self {
        Self {
            parent: Some(parent),
            key: key.clone(),
            children: Self::children_new(),
            is_leaf: false,
        }
    }

    fn children_iter(&self) -> impl Iterator<Item = &Node> {
        self.children.values()
          .map(|b| b.as_ref())
    }

    fn first_leaf(&self) -> Option<&Node> {
            self.is_leaf
              .then_some(self)
              .or_else(|| self.children_iter().find_map(|n| n.first_leaf()))
    }

    fn first_leaf_of_next_sibling(&self) -> Option<&Node> {
        self.get_parent().and_then(|parent| {
                parent
                .children
                .range(self.key..)
                .nth(1)
                .and_then(|(_, child)| child.first_leaf())
        })
    }

    fn next_leaf(cur: Option<&Node>) -> Option<&Node> {
        cur.and_then(|p|
            p.children_iter()
            .next()
            .and_then(|child| child.first_leaf())
            .or_else(|| // Otherwise, walk up to find next sibling subtree
                std::iter::successors(cur, |&n| n.get_parent())
                    .find_map(|n| n.first_leaf_of_next_sibling())
            )
        )
    }

    fn is_root(&self) -> bool {
        self.parent.is_none()
    }
    fn get_parent(&self) -> Option<&Node> {
        self.parent.map(|p| unsafe { p.as_ref() })
    }

    fn id(&self) -> NodeId {
        NodeId(self as *const Node as usize)
    }

    fn from(id: NodeId) -> Option<NonNull<Node>> {
        NonNull::new(id.0 as *mut Node)
    }

    fn key(&self, d: char) -> Option<String> {
        // Reconstruct by walking parents
        let mut parts: Vec<&str> = std::iter::successors(Some(self), |&p| p.get_parent() )
            .take_while(|&p| !p.is_root() )
            .map(|p| p.key.deref() )
            .collect();
        (!parts.is_empty()).then_some({
            parts.reverse();
            let mut buf = [0u8; 4]; // use stack instead of heap allocation (c.to_string() would)
            parts.join(d.encode_utf8(buf.as_mut()))
        })
    }
}

impl<'r, const D: char> Iter<'r, D> {
    pub fn id(&self) -> NodeId {
        self.node.map_or(NodeId(0), |p| p.id())
    }

    pub fn key(&self) -> Option<String> {
        self.node.and_then(|p| p.key(D))
    }

    fn new() -> Self {
        Self { node: None }
    }

    fn from(node: &'r Node) -> Self {
        // ensure we always have a valid ptr or None!
        Self { node: Some(node) }
    }

    fn from_first_leaf(node: &'r Node) -> Self {
        Self { node: node.first_leaf() }
    }
}

impl<'r, const D: char> fmt::Debug for Iter<'r, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(k) = self.key() {
            write!(f, "Iter({k})")
        } else {
            write!(f, "Iter(end)")
        }
    }
}

impl<'r, const D: char> PartialEq for Iter<'r, D> {
    fn eq(&self, other: &Self) -> bool {
        self.node.map(|p| p as *const _) == other.node.map(|p| p as *const _)
    }
}

impl<'r, const D: char> Eq for Iter<'r, D> {}

impl<'r, const D: char> Iterator for Iter<'r, D> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.node.is_none() {
            return None;
        }
        let key = self.key();
        self.node = Node::next_leaf(self.node);
        key
    }
}

impl<'a, const DELIMITER: char> IntoIterator for &'a SegmentedTrieSet<DELIMITER> {
    type Item = String;
    type IntoIter = Iter<'a, DELIMITER>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct RangeIter<'a, const DELIMITER: char> {
    current: Iter<'a, DELIMITER>, // your tree iterator type
    end: Iter<'a, DELIMITER>,     // sentinel end position
}

impl<'a, const DELIMITER: char> RangeIter<'a, DELIMITER> {
    pub fn new(start: Iter<'a, DELIMITER>, end: Iter<'a, DELIMITER>) -> Self {
        RangeIter { current: start, end }
    }
}
impl<'a, const DELIMITER: char> Iterator for RangeIter<'a, DELIMITER> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current == self.end {
            return None;
        }
        self.current.next()
    }
}

#[derive(Clone, Copy)]
struct Key(NonNull<str>);

impl Key {
    fn from_ref(s: &str) -> Self {
        Key(NonNull::from(s))
    }
}

impl Deref for Key {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.0.addr() == other.0.addr()
    }
}
impl Eq for Key {}
impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.deref().cmp(other.deref()))
    }
}
impl Ord for Key {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

// Allow Map lookups by &str.
impl Borrow<str> for Key {
    fn borrow(&self) -> &str {
        self.deref()
    }
}

struct StringPool {
    strings: BTreeSet<String>, // values unused
}

impl StringPool {
    fn new() -> Self {
        Self { strings: BTreeSet::new() }
    }

    fn get_or_insert(&mut self, s: &str) -> &str {
        // very bad, needs 3 lookups, find a better way
        // Entry API ensures only one lookup
        if self.strings.contains(s) {
            return self.strings.get(s).unwrap();
        }
        self.strings.insert(s.to_string());
        self.strings.get(s).unwrap()
    }
}

// cfg-driven children map type: FlatMap when feature "flat_map_children" is enabled,
// otherwise BTreeMap.
#[cfg(feature = "flat_map_children")]
type Children<K, V> = LiteMap<K, V, SplitStore<K, V>>;

#[cfg(feature = "flat_map_children")]
struct SplitStore<K, V> {
    keys: Vec<K>,
    values: Vec<V>,
}

#[cfg(feature = "flat_map_children")]
impl<K: Ord, V> Store<K, V> for SplitStore<K, V> {
    fn lm_len(&self) -> usize {
        self.keys.len()
    }

    fn lm_get(&self, index: usize) -> Option<(&K, &V)> {
        self.keys.get(index).zip(self.values.get(index))
    }

    fn lm_binary_search_by<F>(&self, cmp: F) -> Result<usize, usize>
    where
      F: FnMut(&K) -> Ordering {
        self.keys.binary_search_by(cmp)
    }
}

#[cfg(feature = "flat_map_children")]
impl<K: Ord, V> StoreMut<K, V> for SplitStore<K, V> {
    fn lm_with_capacity(capacity: usize) -> Self {
        Self {
            keys: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
        }
    }

    fn lm_reserve(&mut self, additional: usize) {
        self.keys.reserve(additional);
        self.values.reserve(additional);
    }

    fn lm_get_mut(&mut self, index: usize) -> Option<(&K, &mut V)> {
        self.keys.get(index).zip(self.values.get_mut(index))
    }

    fn lm_push(&mut self, key: K, value: V) {
        self.keys.push(key);
        self.values.push(value);
    }

    fn lm_insert(&mut self, index: usize, key: K, value: V) {
        self.keys.insert(index, key);
        self.values.insert(index, value);
    }

    fn lm_remove(&mut self, index: usize) -> (K, V) {
        let k = self.keys.remove(index);
        let v = self.values.remove(index);
        (k, v)
    }

    fn lm_clear(&mut self) {
        self.keys.clear();
        self.values.clear();
    }
}

#[cfg(not(feature = "flat_map_children"))]
type Children<K, V> = BTreeMap<K, V>;


#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "flat_map_children")]
fn cfg_out() { println!("flat_map_children feature is enabled"); }
#[cfg(not(feature = "flat_map_children"))]
fn cfg_out() { println!("flat_map_children feature is NOT enabled"); }

    #[test]
    fn insert_find_contains_basic() {
        cfg_out();
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id_a = trie.insert("a").unwrap();
        let id_ab = trie.insert("a/b").unwrap();
        assert!(trie.contains("a"));
        assert!(trie.contains("a/b"));
        assert!(!trie.contains("b"));
        assert_ne!(id_a.0, 0);
        assert_ne!(id_ab.0, 0);
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
        let mut trie = SegmentedTrieSet::<'.'>::new();
        ["a.b.1", "a.b.2", "a.c.1", "a.b.4", "a.b.3", "a.b.3.1", "a.c.2", "z"]
            .into_iter()
            .for_each(|key| { let _ = trie.insert(key); });

        let seen: Vec<String> = trie.range("a.b").collect();
        assert_eq!(seen, vec!["a.b.1".to_string(), "a.b.2".to_string(), "a.b.3".to_string(), "a.b.3.1".to_string(), "a.b.4".to_string()]);
    }

    #[test]
    fn find_by_id() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id1 = trie.insert("x/y").unwrap();
        let id2 = trie.insert("x/z").unwrap();
        let id3 = trie.insert("x/x").unwrap();
        // valid id
        let it1 = trie.get_by_id(id1).expect("should find by id");
        assert_eq!(it1.key().unwrap(), "x/y".to_string());
        let it2 = trie.get_by_id(id2).expect("should find by id");
        assert_eq!(it2.key().unwrap(), "x/z".to_string());
        let it3 = trie.get_by_id(id3).expect("should find by id");
        assert_eq!(it3.key().unwrap(), "x/x".to_string());

        assert!(trie.get_by_id(NodeId(0)).is_none());
    }

    #[test]
    fn insert_rejects_empty_segments() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        assert_eq!(trie.insert("/a"), Err(Error::InvalidArg));
        assert_eq!(trie.insert("a//b"), Err(Error::InvalidArg));
        assert_eq!(trie.insert("trail/"), Err(Error::InvalidArg));
        assert_eq!(trie.insert("").err(), Some(Error::InvalidArg));
    }

    #[test]
    fn insert_same_key_twice_errors() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        assert!(trie.insert("a/b").is_ok());
        assert_eq!(trie.insert("a/b"), Err(Error::AlreadyExists));
    }
}