#[cfg(feature = "flat_map_children")]
use flat_map::FlatMap;

use std::borrow::Borrow;
use std::cmp::Ordering;
#[cfg(not(feature = "flat_map_children"))]
use std::collections::BTreeMap;
use std::fmt;
use typed_arena::Arena;

// New small wrapper type used as key in children maps.
// Internally stores a raw pointer to a str that points into the arena (or a static empty str).
#[derive(Clone, Copy)]
struct Key(*const str);

impl Key {
    fn as_str(&self) -> &str {
        // SAFETY: callers must ensure the pointer is valid for the lifetime of the map.
        unsafe { &*self.0 }
    }

    const fn from_static(s: &'static str) -> Self {
        Key(s as *const str)
    }
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}
impl Eq for Key {}
impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.as_str().cmp(other.as_str()))
    }
}
impl Ord for Key {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

// Allow BTreeMap lookups by &str.
impl Borrow<str> for Key {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

#[derive(Debug, PartialEq)]
pub struct NodeId {
    pub value: usize, // pointer address exposed as usize
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsertError {
    InvalidArg,
    KeyAlreadyInserted,
}

// cfg-driven children map type: FlatMap when feature "flat_map_children" is enabled,
// otherwise BTreeMap.
#[cfg(feature = "flat_map_children")]
type Children<K, V> = FlatMap<K, V>;
#[cfg(not(feature = "flat_map_children"))]
type Children<K, V> = BTreeMap<K, V>;

// cfg-driven constructor for the concrete map
#[cfg(feature = "flat_map_children")]
fn children_new<K: Ord, V>() -> Children<K, V> { FlatMap::new() }
#[cfg(not(feature = "flat_map_children"))]
fn children_new<K: Ord, V>() -> Children<K, V> { BTreeMap::new() }

// Simplify: no container family generics here; use BTreeMap for children.
// Children map: key = Key (pointer into arena), value = Box<Node>
pub struct SegmentedTrieSet<const DELIMITER: char> {
    root: Box<Node>,
    segments: Arena<String>,
}

impl<const DELIMITER: char> Default for SegmentedTrieSet<DELIMITER> {
    fn default() -> Self {
        Self {
            root: Box::new(Node::new()),
            segments: Arena::new(),
        }
    }
}

impl<const DELIMITER: char> SegmentedTrieSet<DELIMITER> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> Iter<DELIMITER> {
        Iter::from_first_leaf(&*self.root)
    }

    pub fn contains(&self, key: &str) -> bool {
        self.get(key).is_some()
    }

    pub fn find_by_id(&self, id: NodeId) -> Option<Iter<DELIMITER>> {
        match id.value {
            0 => None,
            _ => Some(Iter::from_ptr(id.value as *const Node)),
        }
    }

    pub fn get(&self, key: &str) -> Option<Iter<DELIMITER>> {
        let root_ptr: *const Node = &*self.root;
        let cur_opt = key
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .fold(Some(root_ptr), |acc, seg| {
                acc.and_then(|cur| unsafe { (&*cur).children.get(seg).map(|b| &**b as *const Node) })
            });

        cur_opt.and_then(|cur| unsafe { if (*cur).is_leaf { Some(Iter::from_ptr(cur)) } else { None } })
    }

    pub fn equal_range(&self, prefix: &str) -> (Iter<DELIMITER>, Iter<DELIMITER>) {
        let root_ptr: *const Node = &*self.root;
        let cur_opt = prefix
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .fold(Some(root_ptr), |acc, seg| {
                acc.and_then(|cur| unsafe { (&*cur).children.get(seg).map(|b| &**b as *const Node) })
            });

        if let Some(cur) = cur_opt {
            if let Some(n) = Node::descend(cur) {
                let begin = Iter::from_ptr(n);
                let end = Node::first_leaf_of_next_sibling(cur)
                    .map(|next| Iter::from_ptr(next))
                    .unwrap_or_else(|| Iter::new());
                return (begin, end);
            }
        }
        (Iter::new(), Iter::new())
    }

    pub fn insert(&mut self, key: &str) -> Result<NodeId, InsertError> {
        if key.is_empty() || key.split(DELIMITER).any(|s| s.is_empty()) {
            return Err(InsertError::InvalidArg);
        }

        let start_ptr: *mut Node = &mut *self.root;
        let res = key
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .fold(Ok(start_ptr) as Result<*mut Node, InsertError>, |acc, seg| {
                acc.and_then(|cur_ptr| unsafe {
                    let cur_node = &mut *cur_ptr;
                    if let Some(child_box) = cur_node.children.get_mut(seg) {
                        return Ok(&mut **child_box as *mut Node);
                    }

                    // allocate segment string in arena as a nonmoving String we can reference on
                    let arena_seg = self.segments.alloc(seg.to_string());
                    let key_ptr = Key(arena_seg.as_str() as *const str);
                    let parent_ptr = cur_node as *const _;

                    // Insert then lookup so both map implementations work
                    cur_node.children.insert(key_ptr, Box::new(Node::new_with_parent(parent_ptr, key_ptr)));
                    cur_node
                        .children
                        .get(seg)
                        .map(|b| &**b as *const Node as *mut Node)
                        .ok_or(InsertError::InvalidArg)
            })
        });
        let cur_ptr = res?;
        unsafe {
            if (*cur_ptr).is_leaf {
                return Err(InsertError::KeyAlreadyInserted);
            }
            (*cur_ptr).is_leaf = true;
            Ok(NodeId {
                value: cur_ptr as usize,
            })
        }
    }
}

// --- Internal pointer-based Node ---

// static empty key used for the root node
static ROOT_EMPTY_KEY: &str = "";

struct Node {
    parent: Option<*const Node>,
    key: Key, // pointer into arena (or static empty for root)
    children: Children<Key, Box<Node>>,
    is_leaf: bool,
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("key", &self.key.as_str())
            .field("is_leaf", &self.is_leaf)
            .finish()
    }
}

impl Node {
    fn new() -> Self {
        Self {
            parent: None,
            key: Key::from_static(ROOT_EMPTY_KEY),
            children: children_new(),
            is_leaf: false,
        }
    }
    fn new_with_parent(parent: *const Node, key: Key) -> Self {
        Self {
            parent: Some(parent),
            key,
            children: children_new(),
            is_leaf: false,
        }
    }

    fn children_iter<'a>(node: *const Node) -> impl Iterator<Item = &'a Node> {
        unsafe { (&*node).children.values().map(|b| &**b) }
    }

    fn descend(start: *const Node) -> Option<*const Node> {
        unsafe {
            let node = &*start;
            if node.is_leaf {
                return Some(start);
            }
            Node::children_iter(start)
                .find_map(|ch| Node::descend(ch as *const _))
        }
    }

    fn first_leaf_of_next_sibling(cur: *const Node) -> Option<*const Node> {
        let parent = unsafe { &*(*cur).parent? };
        // Use iterator combinators: zip the children iterator with itself.skip(1) and
        // find the pair where the first element is `cur`, then descend the second.
        let next = 
            parent
                .children
                .values()
                .zip(parent.children.values().skip(1))
                .find_map(|(a, b)| {
                    if (a.as_ref() as *const Node) == cur {
                        Node::descend(b.as_ref() as *const Node)
                    } else {
                        None
                    }
                });
        next
    }

    fn increment(cur: *const Node) -> Option<*const Node> {
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

// --- Public iterators ---
pub struct Iter<const D: char> {
    node: Option<*const Node>,
}

impl<const D: char> Iter<D> {
    pub fn new() -> Self {
        Self { node: None }
    }

    pub fn id(&self) -> NodeId {
        NodeId {
            value: self.node.map(|p| p as usize).unwrap_or(0),
        }
    }

    fn from_ptr(ptr: *const Node) -> Self {
        Self { node: Some(ptr) }
    }

    fn from_first_leaf(node: *const Node) -> Self {
        if let Some(ptr) = Node::descend(node) {
            Self { node: Some(ptr) }
        } else {
            Self::new()
        }
    }

    fn key(&self) -> Option<String> {
        let node = self.node?;
        // Reconstruct by walking parents
        let mut parts: Vec<&str> =
            std::iter::successors(Some(node), |&p| unsafe { (&*p).parent })
                .map(|p| unsafe { (&*p).key.as_str() })
                .filter(|s| !s.is_empty())
                .collect();
        parts.reverse();
        Some(parts.join(&D.to_string()))
    }
}

impl<const D: char> fmt::Debug for Iter<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(k) = self.key() {
            write!(f, "Iter({k})")
        } else {
            write!(f, "Iter(end)")
        }
    }
}

impl<const D: char> PartialEq for Iter<D> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}

impl<const D: char> Eq for Iter<D> {}

impl<const D: char> Iterator for Iter<D> {
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

impl<const DELIMITER: char> IntoIterator for &SegmentedTrieSet<DELIMITER> {
    type Item = String;
    type IntoIter = Iter<DELIMITER>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

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
        let it1 = trie.find_by_id(id1).expect("should find by id");
        assert_eq!(it1.key().unwrap(), "x/y".to_string());
        let it2 = trie.find_by_id(id2).expect("should find by id");
        assert_eq!(it2.key().unwrap(), "x/z".to_string());
        let it3 = trie.find_by_id(id3).expect("should find by id");
        assert_eq!(it3.key().unwrap(), "x/x".to_string());

        assert!(trie.find_by_id(NodeId { value: 0 }).is_none());
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