#[cfg(feature = "flat_map_children")]
use flat_map::FlatMap;

use std::borrow::Borrow;
use std::cmp::Ordering;
#[cfg(not(feature = "flat_map_children"))]
use std::collections::BTreeMap;
use std::{fmt, ptr};
use std::ptr::NonNull;
use typed_arena::Arena;

///////////////////////////////////////////////////////////////////////
// pub types

#[derive(Debug, PartialEq)]
pub struct NodeId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsertError {
    InvalidArg,
    AlreadyExists,
}

pub struct SegmentedTrieSet<const DELIMITER: char> {
    root: Box<Node>,
    segments: Arena<String>,
}

// --- Public iterators ---
pub struct Iter<const D: char> {
    node: Option<*const Node>,
}

// pub types
///////////////////////////////////////////////////////////////////////
// implementations

impl<const DELIMITER: char> Default for SegmentedTrieSet<DELIMITER> {
    fn default() -> Self {
        Self {
            root: Box::new(Node::default()),
            segments: Arena::new(),
        }
    }
}

impl<const DELIMITER: char> SegmentedTrieSet<DELIMITER> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> Iter<DELIMITER> {
        Iter::from_first_leaf(self.root.as_ref())
    }

    pub fn contains(&self, key: &str) -> bool {
        self.get(key).is_some()
    }

    pub fn get(&self, key: &str) -> Option<Iter<DELIMITER>> {
        self.find_node(key)
            .filter(|cur| cur.is_leaf)
            .map(|cur| Iter::from_ptr(cur))
    }

    pub fn get_by_id(&self, id: NodeId) -> Option<Iter<DELIMITER>> {
        Node::from(id).map(|p| Iter::from_ptr(p))
    }

    fn find_node(&self, prefix: &str) -> Option<&Node> {
        prefix
          .split(DELIMITER)
          .filter(|s| !s.is_empty())
          .fold(Some(&*self.root), |acc, seg| {
              acc.and_then(|cur| cur.children.get(seg).map(|b| b.as_ref()))
          })
    }

    pub fn insert(&mut self, key: &str) -> Result<NodeId, InsertError> {
        if key.is_empty() || key.split(DELIMITER).any(|s| s.is_empty()) {
            return Err(InsertError::InvalidArg);
        }

        let leaf = key
            .split(DELIMITER)
            .fold(self.root.as_mut(), |cur_node, seg| {
                let parent = cur_node as *const _;
                cur_node.children.entry(Key(seg as *const str))
                  .or_insert_with(|| {
                      // allocate segment string in arena as a nonmoving String we can reference on
                      let arena_seg = self.segments.alloc(seg.to_string());
                      Box::new(Node::new_child(parent, Key(arena_seg.as_str() as *const str)))
                  })
        });

        if leaf.is_leaf {
            return Err(InsertError::AlreadyExists);
        }
        leaf.is_leaf = true;
        Ok(leaf.id())
    }

    pub fn equal_range(&self, prefix: &str) -> (Iter<DELIMITER>, Iter<DELIMITER>) {
        self.find_node(prefix)
          .and_then(|cur| {
              cur.descend().map(|n| {
                  (Iter::from_ptr(n), Node::first_leaf_of_next_sibling(cur)
                    .map_or_else(Iter::new, Iter::from_ptr))
              })
          }).unwrap_or_else(|| (Iter::new(), Iter::new()))
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
            key: Key::from_static(""),
            children: Self::children_new(),
            is_leaf: false,
        }
    }
}
impl Node {
    // cfg-driven constructor for the concrete map
    #[cfg(feature = "flat_map_children")]
    fn children_new<K: Ord, V>() -> Children<K, V> { FlatMap::new() }
    #[cfg(not(feature = "flat_map_children"))]
    fn children_new<K: Ord, V>() -> Children<K, V> { BTreeMap::new() }

    fn new_child(parent: *const Node, key: Key) -> Self {
        Self {
            parent: NonNull::new(parent as *mut Node),
            key,
            children: Self::children_new(),
            is_leaf: false,
        }
    }

    fn children_iter(&self) -> impl Iterator<Item = &Node> {
        self.children.values().map(|b| b.as_ref())
    }

    fn descend(&self) -> Option<*const Node> {
            self.is_leaf
              .then_some(self as *const Node)
              .or_else(|| self.children_iter().find_map(|n| n.descend()))
    }

    fn first_leaf_of_next_sibling(&self) -> Option<*const Node> {
        // Use iterator combinators: zip the children iterator with itself.skip(1) and
        // find the pair where the first element is `cur`, then descend the second.
        self.get_parent().and_then(|parent| {
                parent
                .children
                .range(self.key..)
                .nth(1)
                .and_then(|(_, child)| child.descend())
        })
    }

    fn increment(cur: Option<*const Node>) -> Option<*const Node> {
        cur.and_then(|p| unsafe {
            (&*p).children_iter()
            .next()
            .and_then(|child| child.descend())
            .or_else(|| { // Otherwise, walk up to find next sibling subtree
                std::iter::successors(cur, |&n| (&*n).parent.map(|nn| nn.as_ptr() as *const _) )
                    .find_map(|n| (&*n).first_leaf_of_next_sibling())
            })
        })
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

    fn from(id: NodeId) -> Option<*const Node> {
        (id.0 != 0).then_some(id.0 as *const Node)
    }
    
    fn key(&self, d: char) -> Option<String> {
        // Reconstruct by walking parents
        let mut parts: Vec<&str> = std::iter::successors(Some(self), |&p| p.get_parent() )
            .take_while(|&p| !p.is_root() )
            .map(|p| p.key.as_str() )
            .collect();
        (!parts.is_empty()).then_some({
            parts.reverse();
            let mut buf = [0u8; 4]; // use stack instead of heap allocation (c.to_string() would)
            parts.join(d.encode_utf8(buf.as_mut()))
        })
    }
}

impl<const D: char> Iter<D> {
    pub fn id(&self) -> NodeId {
        NodeId(self.node.map_or(0, |p| p as usize))
    }

    pub fn key(&self) -> Option<String> {
        self.node.and_then(|p| unsafe {
            (&*p).key(D)
        })
    }

    fn new() -> Self {
        Self { node: None }
    }

    fn from_ptr(ptr: *const Node) -> Self {
        // ensure we always have a valid ptr or None!
        Self { node: (!ptr.is_null()).then_some(ptr) }
    }

    fn from_first_leaf(node: &Node) -> Self {
        Self { node: node.descend() }
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
        self.node = Node::increment(self.node);
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

#[derive(Clone, Copy)]
struct Key(*const str);

impl Key {
    fn as_str(&self) -> &str {
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

// Allow Map lookups by &str.
impl Borrow<str> for Key {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

// cfg-driven children map type: FlatMap when feature "flat_map_children" is enabled,
// otherwise BTreeMap.
#[cfg(feature = "flat_map_children")]
type Children<K, V> = FlatMap<K, V>;
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

        let (mut begin, end) = trie.equal_range("a.b");
        let seen: Vec<String> = std::iter::from_fn(|| (begin != end)
            .then_some(())
            .and_then(|_| begin.next()))
            .collect();

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
        assert_eq!(trie.insert("/a"), Err(InsertError::InvalidArg));
        assert_eq!(trie.insert("a//b"), Err(InsertError::InvalidArg));
        assert_eq!(trie.insert("trail/"), Err(InsertError::InvalidArg));
        assert_eq!(trie.insert("").err(), Some(InsertError::InvalidArg));
    }

    #[test]
    fn insert_same_key_twice_errors() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        assert!(trie.insert("a/b").is_ok());
        assert_eq!(trie.insert("a/b"), Err(InsertError::AlreadyExists));
    }
}