use std::collections::BTreeMap;
use std::fmt;
use std::ptr::{self, NonNull};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct NodeId {
    pub value: usize, // pointer address exposed as usize
}

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

    pub fn begin(&self) -> Iter<DELIMITER> {
        Iter::from_first_leaf(&self.root)
    }

    pub fn end(&self) -> Iter<DELIMITER> {
        Iter::null()
    }

    // Returns (iterator to leaf, true if inserted new leaf)
    pub fn insert(&mut self, key: &str) -> NodeId{
        let mut cur: *mut Node = &mut self.root;
        for seg in key.split(DELIMITER).filter(|s| !s.is_empty()) {
            // SAFETY: cur points to a valid Node owned by the trie
            cur = unsafe { (*cur).insert_child(seg) };
        }
        let was_leaf = unsafe { (*cur).is_leaf };
        if !was_leaf {
            unsafe { (*cur).is_leaf = true };
        }
        NodeId { value: cur as usize }
    }

    pub fn contains(&self, key: &str) -> bool {
        self.find(key).is_some()
    }

    pub fn find(&self, key: &str) -> Option<Iter<DELIMITER>> {
        let mut cur: *const Node = &self.root;
        for seg in key.split(DELIMITER).filter(|s| !s.is_empty())  {
            // SAFETY: cur points to valid Node
            let next = unsafe { (*cur).find_child(seg) }?;
            cur = next;
        }
        // SAFETY: cur is valid
        let is_leaf = unsafe { (*cur).is_leaf };
        if is_leaf {
            Some(Iter::from_node(cur as *mut Node))
        } else {
            None
        }
    }

    pub unsafe fn find_by_id(&self, id: NodeId) -> Option<Iter<DELIMITER>> {
        if id.value == 0 {
            return None;
        }
        // SAFETY: caller must ensure id is valid; we don't guarantee liveness across mutations
        Some(Iter::from_node(id.value as *mut Node))
    }

    // Return iter over all leaves under prefix; end is exclusive
    pub fn equal_range(&self, prefix: &str) -> (Iter<DELIMITER>, Iter<DELIMITER>) {
        let mut cur: *const Node = &self.root;
        for seg in prefix.split(DELIMITER).filter(|s| !s.is_empty())  {
            cur = match unsafe { (*cur).find_child(seg) } {
                Some(n) => n,
                None => return (Iter::null(), Iter::null())
            };
        }

        // First leaf under this node
        let first_leaf = unsafe { Node::descend(cur) };
        if first_leaf.is_none() {
            return (Iter::null(), Iter::null());
        }

        // End is the first leaf of the next sibling subtree (exclusive), or None
        let end = unsafe { Node::first_leaf_of_next_subtree(cur) };

        unsafe {
            (Iter::from_first_leaf(&*first_leaf.unwrap()), Iter::from_first_leaf(&*end.unwrap()))
        }
    }
}

// --- Internal Node ---

struct Node {
    parent: Option<NonNull<Node>>,
    key: String, // segment at this node (empty for root)
    children: BTreeMap<String, Box<Node>>,
    is_leaf: bool,
}

impl Node {
    fn new() -> Self {
        Self {
            parent: None,
            key: String::new(),
            children: BTreeMap::new(),
            is_leaf: false,
        }
    }

    fn new_child(parent: *mut Node, key: &str) -> Box<Node> {
        let node = Box::new(Self {
            parent: NonNull::new(parent),
            key: key.to_string(),
            children: BTreeMap::new(),
            is_leaf: false,
        });
        node
    }

    // SAFETY: self must be valid; returns pointer to child (owned by self)
    unsafe fn insert_child(&mut self, seg: &str) -> *mut Node {
        if seg.is_empty() {
            return self as *mut Node;
        }
        if let Some(child) = self.children.get_mut(seg) {
            return &mut **child as *mut Node;
        }
        let mut child = Self::new_child(self as *mut Node, seg);
        let ptr: *mut Node = &mut *child;
        self.children.insert(seg.to_string(), child);
        ptr
    }

    unsafe fn find_child(&self, seg: &str) -> Option<*const Node> {
        if seg.is_empty() {
            return Some(self as *const Node);
        }
        self.children.get(seg).map(|b| &**b as *const Node)
    }

    unsafe fn descend(n: *const Node) -> Option<*mut Node> {
        unsafe {
            if (*n).is_leaf {
                return Some(n as *mut Node);
            }
            for (_, child) in (*n).children.iter() {
                let leaf = Node::descend(&**child as *const Node);
                if leaf.is_some() {
                    return leaf;
                }
            }
        }
        None
    }

    unsafe fn increment(mut cur: *const Node) -> Option<*mut Node> {
        loop {
            unsafe {
                let parent = match (*cur).parent {
                    Some(nn) => nn.as_ptr(),
                    None => return None,
                };

                let mut it = (*parent).children.range((*cur).key.clone()..);
                let _self = it.next(); // current
                if let Some((_, next_child)) = it.next() {
                    let start = &**next_child as *const Node;
                    return Self::descend(start).map(|p| p as *mut Node);
                }
                cur = parent;
            }
        }
    }

    unsafe fn first_leaf_of_next_subtree(cur: *const Node) -> Option<*mut Node> {
        // If cur has a parent, find next sibling of cur and descend
        unsafe {
            let parent = match (*cur).parent {
                Some(nn) => nn.as_ptr(),
                None => return None,
            };
            let mut it = (*parent).children.range((*cur).key.clone()..);
            it.next(); // skip self
            if let Some((_, it_next)) = it.next() {
                return Self::descend(&**it_next as *const Node);
            }
        }
        None
    }
}


// --- Public iterators ---
pub struct Iter<const D: char> {
    node: *mut Node,
}

impl<const D: char> Iter<D> {
    fn null() -> Self {
        Self { node: ptr::null_mut() }
    }

    fn from_node(n: *mut Node) -> Self {
        Self { node: n }
    }

    fn from_first_leaf(root: &Node) -> Self {
        // SAFETY: root is valid
        let first = unsafe { Node::descend(root as *const Node) };
        match first {
            Some(n) => Self { node: n },
            None => Self::null(),
        }
    }

    pub fn id(&self) -> NodeId {
        NodeId { value: self.node as usize }
    }

    pub fn is_end(&self) -> bool {
        self.node.is_null()
    }

    pub fn next(&mut self) {
        if self.node.is_null() {
            return;
        }
        // SAFETY: self.node is valid leaf
        self.node = unsafe { Node::increment(self.node as *const Node) }.unwrap_or(ptr::null_mut());
    }

    pub fn key(&self) -> Option<String> {
        if self.node.is_null() {
            return None;
        }
        // Reconstruct by walking parents
        let mut key = String::new();
        unsafe {
            let mut cur = self.node as *const Node;
            loop {
                key.insert_str(0, &(*cur).key);
                match (*cur).parent {
                    Some(nn) => {
                        key.insert(0, D);
                        cur = nn.as_ptr();
                    }
                    None => break,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_find_contains_basic() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id_a = trie.insert("/a");
        let id_ab = trie.insert("/a/b");
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
        trie.insert("/a/b");
        trie.insert("/a/c");
        trie.insert("/b");
        trie.insert("/a"); // make "a" a leaf too

        let mut it = trie.begin();
        let mut keys = Vec::new();
        while !it.is_end() {
            keys.push(it.key().unwrap());
            it.next();
        }

        // Expected traversal: "a" (leaf) then "a/b" then "a/c" then "b"
        assert_eq!(keys, vec!["a".to_string(), "a/b".to_string(), "a/c".to_string(), "b".to_string()]);
    }

    #[test]
    fn equal_range_prefix_collects_expected() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        trie.insert("/a/b/1");
        trie.insert("/a/b/2");
        trie.insert("/a/c/1");
        trie.insert("/z");

        // range for "/a/b" should include "a/b/1" and "a/b/2" and end at first leaf of next sibling subtree ("a/c/1")
        let (mut begin, end) = trie.equal_range("/a/b");
        let mut seen = Vec::new();
        while begin.id() != end.id() && !begin.is_end() {
            seen.push(begin.key().unwrap());
            begin.next();
        }

        assert_eq!(seen, vec!["a/b/1".to_string(), "a/b/2".to_string()]);
    }

    #[test]
    fn find_by_id_and_invalid_zero() {
        let mut trie = SegmentedTrieSet::<'/'>::new();
        let id = trie.insert("/x/y");
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
}