use std::collections::BTreeSet;
use std::cmp::Ordering;
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

    pub fn insert(&mut self, key: &str) -> NodeId{
        let mut cur: *mut Node = &mut self.root;
        for seg in key.split(DELIMITER).filter(|s| !s.is_empty()) {
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
    children: BTreeSet<Box<Node>>,
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
            children: BTreeSet::new(),
            is_leaf: false,
        }
    }

    fn new_child(parent: *mut Node, key: &str) -> Box<Node> {
        let node = Box::new(Self {
            parent: NonNull::new(parent),
            key: key.to_string(),
            children: BTreeSet::new(),
            is_leaf: false,
        });
        node
    }

    // SAFETY: self must be valid; returns pointer to child (owned by self)
    unsafe fn insert_child(&mut self, seg: &str) -> *mut Node {
        if seg.is_empty() {
            return self as *mut Node;
        }
        if let Some(ptr) = unsafe { self.find_child(seg) } {
            return ptr as *mut Node;
        }
        // Create and insert new child
        let child = Self::new_child(self as *mut Node, seg);
        let ptr: *mut Node = &*child as *const Node as *mut Node;
        self.children.insert(child);
        ptr
    }

    unsafe fn find_child(&self, seg: &str) -> Option<*const Node> {
        if seg.is_empty() {
            return Some(self as *const Node);
        }
        // Use iterator helper to locate the child without a manual loop
        self.children
            .iter()
            .find(|child| child.key == seg)
            .map(|child| &**child as *const Node)
    }

    unsafe fn descend(n: *const Node) -> Option<*mut Node> {
        unsafe {
            if (*n).is_leaf {
                return Some(n as *mut Node);
            }
            (*n)
                .children
                .iter()
                .find_map(|child| Node::descend(&**child as *const Node))
        }
    }

    unsafe fn increment(mut cur: *const Node) -> Option<*mut Node> {
        // `from_child` is true when we've just climbed up from a child.
        // When climbing up we must not immediately descend into the parent's
        // first child (that would re-enter the subtree we came from and loop).
        let mut from_child = false;
        loop {
            unsafe {
                // Only descend into children when we are at the node itself
                // (i.e. not when we've just climbed from one of its children).
                if !from_child && !(*cur).children.is_empty() {
                    let first_child = (*cur).children.iter().next()?;
                    return Self::descend(&**first_child as *const Node).map(|p| p as *mut Node);
                }

                let parent = match (*cur).parent {
                    Some(nn) => nn.as_ptr(),
                    None => return None,
                };

                let cur_key = &(*cur).key;
                let mut found_self = false;
                for child in &(*parent).children {
                    if found_self {
                        let start = &**child as *const Node;
                        return Self::descend(start).map(|p| p as *mut Node);
                    }
                    if &child.key == cur_key {
                        found_self = true;
                    }
                }

                // climb up and mark that we came from a child so the next
                // iteration doesn't re-descend into the same parent's children
                cur = parent;
                from_child = true;
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
            let cur_key = &(*cur).key;
            let mut found_self = false;
            for child in &(*parent).children {
                if found_self {
                    return Self::descend(&**child as *const Node);
                }
                if &child.key == cur_key {
                    found_self = true;
                }
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