use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt;
use std::ptr::{self, NonNull};

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
pub struct SegmentedTrieSet<const DELIMITER: char> {
    root: Node,
}

impl<const DELIMITER: char> Default for SegmentedTrieSet<DELIMITER> {
    fn default() -> Self {
        Self { root: Node::new() }
    }
}

impl<const DELIMITER: char> SegmentedTrieSet<DELIMITER> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> Iter<DELIMITER> {
        Iter::from_first_leaf(&self.root)
    }

    pub fn find(&self, key: &str) -> Option<Iter<DELIMITER>> {
        let cur = key
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .try_fold(&self.root as *const Node, |cur, seg| {
                // SAFETY: cur points to valid Node
                unsafe { (*cur).find_child(seg) }
            })?;
        if !cur.is_null() && unsafe { (*cur).is_leaf } {
            return Some(Iter::from_node(cur as *mut Node));
        }
        None
    }

    pub fn equal_range(&self, prefix: &str) -> (Iter<DELIMITER>, Iter<DELIMITER>) {
        let cur = prefix
            .split(DELIMITER)
            .filter(|s| !s.is_empty())
            .fold(&self.root as *const Node, |cur, seg| {
                unsafe { (*cur).find_child(seg) }
            });

        let mut end: Iter<DELIMITER> = Iter::new();
        let begin = unsafe {
            let n = Node::descend(cur);
            if !n.is_null() {
                if let Some(next) = Node::first_leaf_of_next_subtree(cur) {
                    end = Iter::from_first_leaf(&*next);
                }
                Iter::from_first_leaf(&*n)
            } else {
                Iter::new()
            }
        };

        (begin, end)
    }

    pub fn insert(&mut self, key: &str) -> Result<NodeId, InsertError> {
        let mut keys: Vec<&str> = Vec::new();
        let mut node = key
                .split(DELIMITER)
                .try_fold(&mut self.root as *mut Node, |cur_ptr, seg| {
            if seg.is_empty() {
                return Err(InsertError::InvalidArg);
            }
            let mut ret = cur_ptr;
            if keys.is_empty() {
                let child = unsafe { (*cur_ptr).find_child(seg) };
                if child.is_null() {
                    keys.push(seg);
                } else {
                    ret = child as *mut Node;
                }
            }
            else {
                keys.push(seg);
            }
            Ok(ret)
        })?;

        // Insert new children for recorded segments
        keys.iter().for_each(|seg| unsafe { node = (*node).insert_child(seg) });

        // If the node is already marked as a leaf, the key already exists
        unsafe {
             if (*node).is_leaf {
                return Err(InsertError::KeyAlreadyInserted);
            }
            (*node).is_leaf = true
        };
        Ok(NodeId { value: node as usize })
    }

    pub fn contains(&self, key: &str) -> bool {
        self.find(key).is_some()
    }

    pub unsafe fn find_by_id(&self, id: NodeId) -> Option<Iter<DELIMITER>> {
        // SAFETY: caller must ensure id is valid; we don't guarantee liveness across mutations
        std::num::NonZeroUsize::new(id.value)
            .map(|nz| Iter::from_node(nz.get() as *mut Node))
    }
}

// --- Internal Node ---

// Ensure that the Node is not moving in memory
// if the set is BTreeSet, we could use Node instead of Box<Node>
// but I want to replace BTreeSet with a FlatSet (need to compare performance/memory usage)
// Unfortunately, there is currently no crate with a FlatSet implementation
type NodeType = Box<Node>;
type ContainerType = BTreeSet<NodeType>;

#[derive(Debug)]
struct Node {
    parent: Option<NonNull<Node>>,
    key: String, // segment at this node (empty for root)
    children: ContainerType,
    is_leaf: bool,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for Node {}

impl PartialOrd for Node {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Node {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

impl Node {
    fn new() -> Self {
        Self {
            parent: None,
            key: String::new(),
            children: ContainerType::new(),
            is_leaf: false,
        }
    }

    fn new_child(parent: *mut Node, key: &str) -> NodeType {
        let node = NodeType::new(Self {
            parent: NonNull::new(parent),
            key: key.to_string(),
            children: ContainerType::new(),
            is_leaf: false,
        });
        node
    }

    // helper: iterate over children as &Node
    fn children_iter(&self) -> impl Iterator<Item = &Node> {
        self.children.iter().map(|b| &**b)
    }

    // helper: find the next sibling of `cur` in its parent and descend to the first leaf.
    // returns null pointer when not found.
    fn first_leaf_of_next_sibling(cur: *const Node) -> *mut Node {
        unsafe {
            let parent = match (*cur).parent {
                Some(nn) => nn.as_ptr(),
                None => return ptr::null_mut(),
            };
            let cur_key = (*cur).key.as_str();
            if let Some(next_child) = (*parent)
                .children_iter()
                .skip_while(|child| child.key != cur_key)
                .nth(1)
            {
                let res = Self::descend(next_child as *const Node);
                if !res.is_null() {
                    return res;
                }
            }
        }
        ptr::null_mut()
    }

    // SAFETY: self must be valid; returns pointer to child (owned by self)
    unsafe fn insert_child(&mut self, seg: &str) -> *mut Node {
        let child = Self::new_child(self as *mut Node, seg);
        let ptr: *mut Node = &*child as *const Node as *mut Node;
        self.children.insert(child);
        ptr
    }

    unsafe fn find_child(&self, seg: &str) -> *const Node {
        if seg.is_empty() {
            return self as *const Node;
        }
        // Use iterator helper to locate the child without a manual loop
        self.children_iter()
            .find(|child| child.key == seg)
            .map(|child| child as *const Node)
            .unwrap_or(ptr::null())
    }

    // changed: return raw pointer (null on failure) instead of Option
    fn descend(n: *const Node) -> *mut Node {
        unsafe {
            if (*n).is_leaf {
                return n as *mut Node;
            }
            (&*n)
                .children_iter()
                .find_map(|child| {
                    let res = Node::descend(child as *const Node);
                    if !res.is_null() { Some(res) } else { None }
                })
                .unwrap_or(ptr::null_mut())
        }
    }

    unsafe fn increment(mut cur: *const Node) -> *mut Node {
        unsafe {
            if !(*cur).children.is_empty() {
                let first_child = (*cur).children_iter().next().unwrap();
                let res = Self::descend(first_child as *const Node);
                if !res.is_null() {
                    return res;
                }
                return ptr::null_mut();
            }

            while let Some(parent_nn) = (*cur).parent {
                // try to find a next-sibling subtree and descend into its first leaf
                let res = Self::first_leaf_of_next_sibling(cur);
                if !res.is_null() {
                    return res;
                }
                // move up to parent and continue searching
                cur = parent_nn.as_ptr() as *const Node;
            }

            ptr::null_mut()
        }
    }

    fn first_leaf_of_next_subtree(cur: *const Node) -> Option<*mut Node> {
        let res = Self::first_leaf_of_next_sibling(cur);
        if res.is_null() { None } else { Some(res) }
    }
}


// --- Public iterators ---
pub struct Iter<const D: char> {
    node: *mut Node,
}

impl<const D: char> Iter<D> {
    pub fn new() -> Self {
        Self { node: ptr::null_mut() }
    }

    pub fn id(&self) -> NodeId {
        NodeId { value: self.node as usize }
    }

    fn from_node(n: *mut Node) -> Self {
        Self { node: n }
    }

    fn from_first_leaf(root: &Node) -> Self {
        let n = Node::descend(root as *const Node);
        if !n.is_null() {
            Self { node: n }
        } else {
            Self::new()
        }
    }

    fn key(&self) -> Option<String> {
        if self.node.is_null() {
            return None;
        }
        // Reconstruct by walking parents
        let mut key = String::new();
        let mut cur = self.node as *const Node;
        while cur != ptr::null() {
            unsafe {
                key.insert_str(0, &(*cur).key);
                match (*cur).parent {
                    Some(nn) => {
                        cur = nn.as_ptr();
                        // Only insert delimiter if parent's parent exists (not root)
                        if (*cur).parent.is_some() {
                            key.insert(0, D);
                        }
                    }
                    None => cur = ptr::null(),
                }
            }
        }
        Some(key)
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
        if self.node.is_null() {
            return None;
        }
        let key = self.key();
        // SAFETY: self.node is a valid leaf; advance to next leaf or end (null)
        self.node = unsafe { Node::increment(self.node as *const Node) };
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

    #[test]
    fn insert_find_contains_basic() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id_a = trie.insert("/a").unwrap();
        let id_ab = trie.insert("/a/b").unwrap();
        assert!(trie.contains("/a"));
        assert!(trie.contains("/a/b"));
        assert!(!trie.contains("/b"));
        // check ids are non-zero
        assert_ne!(id_a.value, 0);
        assert_ne!(id_ab.value, 0);
    }

    #[test]
    fn iterator_order_and_keys() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let _ = trie.insert("a/b");
        let _ = trie.insert("a/c");
        let _ = trie.insert("b");
        let _ = trie.insert("a"); // make "a" a leaf too

        let keys: Vec<String> = trie.iter().collect();

        // Expected traversal: "a" (leaf) then "a/b" then "a/c" then "b"
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

        // range for "/a/b" should include "a/b/1" and "a/b/2" and end at first leaf of next sibling subtree ("a/c/1")
        let (mut begin, end) = trie.equal_range("a/b");
        let mut seen: Vec<String> = Vec::new();
        while begin != end {
            if let Some(k) = begin.next() { seen.push(k); } else { break; }
        }

        assert_eq!(seen, vec!["a/b/1".to_string(), "a/b/2".to_string()]);
    }

    #[test]
    fn find_by_id_and_invalid_zero() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id = trie.insert("/x/y").unwrap();
        // valid id
        unsafe {
            let it = trie.find_by_id(id).expect("should find by id");
            assert_eq!(it.key().unwrap(), "x/y".to_string());
        }
        // zero id is considered None
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