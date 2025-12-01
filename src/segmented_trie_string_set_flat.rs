use core::fmt;
use flat_map::FlatMap;
use std::iter::Iterator;
use std::ptr;

/// A variant of SegmentedTrieStringSet where each node's children are stored in a
/// FlatMap.
/// Trade-offs vs the BTreeMap-backed version:
/// - Pros: fewer heap nodes, cache-friendly iteration; deterministic order.
/// - Cons: insert/remove are O(k * log n + n) per level due to Vec shifts.
///
/// Semantics are identical to SegmentedTrieStringSet: keys are split by a
/// delimiter char; each edge stores an entire segment; empty segments are
/// preserved.
pub struct SegmentedTrieStringSetFlat {
    root: Box<Node>,
    len: usize,
    delim: char,
}

pub struct Node {
    parent: *mut Node,
    key: String,
    children: FlatMap<String, Box<Node>>,
    terminal: bool,
}

pub struct Iter<'a> {
    current: Option<&'a Node>,
}

impl<'a> Iter<'a> {
    pub fn new(n: &'a Node) -> Iter<'a> {
        Iter { current: Some(n) }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = (String, crate::TrieSetId);

    fn next(&mut self) -> Option<Self::Item> {
        let mut node = self.current?;
        loop {
            if let Some((_, child)) = node.children.iter().find(|(_, c)| c.terminal ) {
                node = child;
                break;
            }
            if node.parent.is_null() {
                return None;
            }
            unsafe {
                node = &mut *node.parent;
            }
        }
        if node.terminal == false {
            return None;
        }
        let addr = node as *const Node as usize;
        let ret = Some((node.key.clone(), crate::TrieSetId { addr }));
        self.current = Some(node);
        ret
    }
}

impl Default for SegmentedTrieStringSetFlat {
    fn default() -> Self {
        Self { root: Box::new(Node::default()), len: 0, delim: '.' }
    }
}

impl Default for Node {
    fn default() -> Self { Self {
        parent: ptr::null_mut(), key: String::new(), children: FlatMap::new(), terminal: false }
    }
}

impl fmt::Debug for SegmentedTrieStringSetFlat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Print as a set of escaped byte strings
        struct Disp<'a>(&'a SegmentedTrieStringSetFlat);
        impl<'a> fmt::Debug for Disp<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                todo!()
            }
        }
        fmt::Debug::fmt(&Disp(self), f)
    }
}

impl SegmentedTrieStringSetFlat {
    pub fn new() -> Self { Self::default() }

    /// Create a set using the provided delimiter byte for segmentation.
    pub fn with_delimiter(delim: char) -> Self { Self { delim, ..Self::default() } }

    #[inline]
    pub fn len(&self) -> usize { self.len }

    #[inline]
    pub fn is_empty(&self) -> bool { self.len == 0 }

    pub fn clear(&mut self) {
        self.root = Box::new(Node::default());
        self.len = 0;
    }

    /// Insert a key.
    ///
    /// Returns a unique Some(TrieSetId) if the key was newly inserted.
    /// Returns None if the key was already present or if the key is empty.
    pub fn insert(&mut self, key: &str) -> Option<crate::TrieSetId> {
        if key.is_empty() { return None; }
        let mut node: &mut Node = self.root.as_mut();
        for seg in key.split(self.delim) {
            // Preserve empty segments; they are valid edges
            let p = node as *mut Node;
            let entry = node
                .children
                .entry(seg.to_string())
                .or_insert_with(|| Box::new(Node { parent: p, key: seg.to_string(), children: FlatMap::new(), terminal: false }));
            node = entry;
        }
        if node.terminal {
            None
        } else {
            node.terminal = true;
            self.len += 1;
            let addr = (node as *mut Node) as usize;
            Some(crate::TrieSetId { addr })
        }
    }

    /// Returns true if the key is present.
    pub fn contains(&self, key: &str) -> bool {
        if key.is_empty() { return false; }
        let mut node: &Node = self.root.as_ref();
        for seg in key.split(self.delim) {
            match node.children.get(seg) {
                Some(next) => node = next,
                None => return false,
            }
        }
        node.terminal
    }

    /// Removes a key. Returns true if the key was present.
    pub fn remove(&mut self, key: &str) -> bool {
        let segs: Vec<&str> = key.split(self.delim).rev().collect();
        true
    }

    pub fn iter(&self) -> Iter<'_> { Iter::new(&self.root) }
    pub fn get(&self, id: crate::TrieSetId) -> String {
        let ptr = id.addr as *const Node;
        let mut node = unsafe { &*ptr };
        let mut s = node.key.clone();
        while node.parent != ptr::null_mut() {
            node = unsafe { &*node.parent };
            s.insert(0, self.delim);
            s.insert_str(0, node.key.as_ref());
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_string_ops_flat() {
        let mut s = SegmentedTrieStringSetFlat::new();
        assert!(s.insert("").is_none()); // empty string not allowed
        assert!(!s.contains(""));
        assert!(s.insert("").is_none());

        assert!(s.insert("a").is_some());
        assert!(s.insert("ab").is_some());
        assert!(s.contains("a"));
        assert!(s.contains("ab"));
        assert!(!s.contains("abc"));

        assert!(s.remove("a"));
        assert!(!s.contains("a"));
        assert!(s.contains("ab"));
        assert!(!s.remove("a"));
    }

    #[test]
    fn segmented_by_dot_flat() {
        let mut s = SegmentedTrieStringSetFlat::new(); // default '.'
        assert!(s.insert("a").is_some());
        assert!(s.insert("a.b").is_some());
        assert!(s.insert("a.b.c").is_some());
        assert!(s.contains("a"));
        assert!(s.contains("a.b"));
        assert!(s.contains("a.b.c"));
        assert!(!s.contains("a.c"));

        // empty segments preserved
        assert!(s.insert("a..b").is_some());
        assert!(s.contains("a..b"));
        assert!(s.insert(".lead").is_some());
        assert!(s.contains(".lead"));
        assert!(s.insert("trail.").is_some());
        assert!(s.contains("trail."));

        // removal prunes properly and doesn't affect siblings
        assert!(s.remove("a.b"));
        assert!(!s.contains("a.b"));
        assert!(s.contains("a.b.c"));
        assert!(s.contains("a"));
    }
}
