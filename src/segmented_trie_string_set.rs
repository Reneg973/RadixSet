use core::fmt;
use std::collections::BTreeMap;

/// A set of byte strings (e.g., UTF-8 `&str` or arbitrary `&[u8]`) where each
/// key is split into segments by a delimiter byte, and each trie edge holds a
/// full segment (substring) like the referenced C++ SegmentedTrie.
///
/// - Default delimiter is '.' (0x2E). Use `with_delimiter` to choose another.
/// - Splitting preserves empty segments (leading, trailing, or consecutive
///   delimiters), so keys like ".a", "a.", and "a..b" are all represented
///   precisely.
/// - Accepts any key type implementing `AsRef<[u8]>` similar to C++'s
///   `std::string_view`.
pub struct SegmentedTrieStringSet {
    root: Box<Node>,
    len: usize,
    delim: u8,
}

pub struct Node {
    children: BTreeMap<Vec<u8>, Box<Node>>, // edge label is a whole segment, kept sorted
    terminal: bool,
}

impl Default for SegmentedTrieStringSet {
    fn default() -> Self {
        Self { root: Box::new(Node::default()), len: 0, delim: b'.' }
    }
}

impl Default for Node {
    fn default() -> Self {
        Self { children: BTreeMap::new(), terminal: false }
    }
}

impl fmt::Debug for SegmentedTrieStringSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Print as a set of escaped byte strings
        struct Disp<'a>(&'a SegmentedTrieStringSet);
        impl<'a> fmt::Debug for Disp<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let items: Vec<Vec<u8>> = self.0.iter_bytes().collect();
                let mut set = f.debug_set();
                for b in items {
                    // Try UTF-8 first for readability, fall back to byte escape
                    match String::from_utf8(b.clone()) {
                        Ok(s) => {
                            set.entry(&s);
                        }
                        Err(_) => {
                            struct Bytes(Vec<u8>);
                            impl fmt::Display for Bytes {
                                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                                    for &c in &self.0 { write!(f, "\\x{:02x}", c)?; }
                                    Ok(())
                                }
                            }
                            set.entry(&format_args!("{}", Bytes(b)));
                        }
                    }
                }
                set.finish()
            }
        }
        fmt::Debug::fmt(&Disp(self), f)
    }
}

impl SegmentedTrieStringSet {
    pub fn new() -> Self { Self::default() }

    /// Create a set using the provided delimiter byte for segmentation.
    pub fn with_delimiter(delim: u8) -> Self { Self { delim, ..Self::default() } }

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
    /// Returns Some(TrieSetId) containing the node's address if the key was newly inserted
    /// as a terminal. Returns None if the key was already present or if the key is empty.
    pub fn insert<K: AsRef<[u8]>>(&mut self, key: K) -> Option<crate::TrieSetId> {
        let bytes = key.as_ref();
        if bytes.is_empty() { return None; }
        let mut node: &mut Node = self.root.as_mut();
        for seg in bytes.split(|&b| b == self.delim) {
            // Own the segment bytes for the edge key
            let entry = node.children.entry(seg.to_vec()).or_insert_with(|| Box::new(Node::default()));
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
    pub fn contains<K: AsRef<[u8]>>(&self, key: K) -> bool {
        let mut node: &Node = self.root.as_ref();
        for seg in key.as_ref().split(|&b| b == self.delim) {
            match node.children.get(seg) {
                Some(next) => node = next,
                None => return false,
            }
        }
        node.terminal
    }

    /// Removes a key. Returns true if the key was present.
    pub fn remove<K: AsRef<[u8]>>(&mut self, key: K) -> bool {
        let segs: Vec<&[u8]> = key.as_ref().split(|&b| b == self.delim).collect();
        let removed = Self::remove_inner(self.root.as_mut(), &segs, 0);
        if removed { self.len -= 1; true } else { false }
    }

    fn remove_inner(node: &mut Node, segs: &[&[u8]], idx: usize) -> bool {
        if idx == segs.len() {
            if node.terminal { node.terminal = false; true } else { false }
        } else {
            let key = segs[idx];
            if let Some(child) = node.children.get_mut(key) {
                let removed = Self::remove_inner(child, segs, idx + 1);
                if removed {
                    if !child.terminal && child.children.is_empty() {
                        // prune
                        node.children.remove(key);
                    }
                }
                removed
            } else {
                false
            }
        }
    }

    /// Iterate over all keys as owned byte vectors in lexicographic order.
    pub fn iter_bytes(&self) -> impl Iterator<Item = Vec<u8>> + '_ {
        let mut out = Vec::with_capacity(self.len);
        let mut buf = Vec::new();
        self.collect(self.root.as_ref(), 0, &mut buf, &mut out);
        out.into_iter()
    }

    fn collect(&self, node: &Node, seg_count: usize, buf: &mut Vec<u8>, out: &mut Vec<Vec<u8>>) {
        if node.terminal { out.push(buf.clone()); }
        for (seg, child) in node.children.iter() {
            let mut added = 0usize;
            if seg_count > 0 { buf.push(self.delim); added += 1; }
            buf.extend_from_slice(seg); added += seg.len();
            self.collect(child, seg_count + 1, buf, out);
            let new_len = buf.len() - added;
            buf.truncate(new_len);
        }
    }

    // Logical ID support removed as superfluous; raw node addresses can be used if needed.

    /// Returns the raw address (usize) of the terminal node for this key, if it exists.
    /// This mirrors using the node's address as a unique identifier, like in C++.
    /// Note: The address is only valid while the node is alive; after removal, it may be reused.
    pub fn addr_id_of<K: AsRef<[u8]>>(&mut self, key: K) -> Option<usize> {
        let bytes = key.as_ref();
        let mut node: &mut Node = self.root.as_mut();
        for seg in bytes.split(|&b| b == self.delim) {
            match node.children.get_mut(seg) {
                Some(next) => node = next,
                None => return None,
            }
        }
        if !node.terminal { return None; }
        let addr = (node as *mut Node) as usize;
        Some(addr)
    }

    /// UNSAFE: Cast a previously obtained raw node address back to a shared reference.
    ///
    /// Safety:
    /// - The provided `addr` must have come from a prior call to `addr_id_of` on this very
    ///   instance, and that node must still be alive (i.e., the key has not been removed and
    ///   the set has not been cleared). No runtime liveness checks are performed.
    /// - You must not create aliasing mutable references that violate Rust's aliasing rules.
    /// - The returned reference is tied to `&self`; do not use it after mutating the set in a way
    ///   that could remove or replace that node.
    pub unsafe fn node_from_addr<'a>(&'a self, addr: usize) -> Option<&'a Node> {
        let ptr = addr as *const Node;
        // SAFETY: caller upholds that `addr` is valid for the lifetime of `&self` and non-aliasing
        let r = unsafe { &*ptr };
        Some(r)
    }

    /// UNSAFE: Cast a previously obtained raw node address back to a unique mutable reference.
    ///
    /// Safety:
    /// - All requirements from `node_from_addr` apply. No runtime liveness checks are performed.
    /// - Additionally, you must ensure no other references (shared or mutable) to the same node
    ///   are alive when calling this. Violating this is undefined behavior.
    pub unsafe fn node_from_addr_mut<'a>(&'a mut self, addr: usize) -> Option<&'a mut Node> {
        let ptr = addr as *mut Node;
        // SAFETY: caller guarantees unique access and valid pointer
        let r = unsafe { &mut *ptr };
        Some(r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_string_ops() {
        let mut s = SegmentedTrieStringSet::new();
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
    fn bytes_and_utf8() {
        let mut s = SegmentedTrieStringSet::new();
        let bytes = [0u8, 255, 128];
        assert!(s.insert(&bytes).is_some());
        assert!(s.contains(&bytes));
        // valid UTF-8
        assert!(s.insert("hé").is_some());
        assert!(s.contains("hé"));
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn segmented_by_dot() {
        let mut s = SegmentedTrieStringSet::new(); // default '.'
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

    #[test]
    fn iteration_is_sorted_root_children() {
        let mut s = SegmentedTrieStringSet::new();
        assert!(s.insert("b").is_some());
        assert!(s.insert("a").is_some());
        assert!(s.insert("c").is_some());
        let got: Vec<String> = s
            .iter_bytes()
            .map(|v| String::from_utf8(v).unwrap())
            .collect();
        assert_eq!(got, vec!["a", "b", "c"]);
    }

    #[test]
    fn iteration_is_sorted_under_same_prefix() {
        let mut s = SegmentedTrieStringSet::new();
        assert!(s.insert("a.c").is_some());
        assert!(s.insert("a.a").is_some());
        assert!(s.insert("a.b").is_some());
        assert!(s.insert("a").is_some());
        let got: Vec<String> = s
            .iter_bytes()
            .map(|v| String::from_utf8(v).unwrap())
            .collect();
        assert_eq!(got, vec!["a", "a.a", "a.b", "a.c"]);
    }

    #[test]
    fn no_op_placeholder_to_keep_tests_compiling() {}

    #[test]
    fn addr_id_assign_lookup_and_remove() {
        let mut s = SegmentedTrieStringSet::new();
        s.insert("a");
        s.insert("a.b");

        // No addr for non-existent
        assert!(s.addr_id_of("x").is_none());

        let addr_a = s.addr_id_of("a").unwrap();
        let addr_ab = s.addr_id_of("a.b").unwrap();
        assert_ne!(addr_a, addr_ab);
        // Stable on repeat (same node address)
        assert_eq!(Some(addr_a), s.addr_id_of("a"));

        // Remove and ensure removal took effect
        assert!(s.remove("a"));
        assert!(!s.contains("a"));
    }

    #[test]
    fn unsafe_round_trip_addr_to_node() {
        let mut s = SegmentedTrieStringSet::new();
        s.insert("a.b");
        let addr = s.addr_id_of("a.b").unwrap();
        // Round-trip: address -> &Node should point to same address
        let got_addr = unsafe {
            let nref = s.node_from_addr(addr).unwrap();
            (nref as *const Node) as usize
        };
        assert_eq!(addr, got_addr);
    }
}
