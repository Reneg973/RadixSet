use core::fmt;

/// A set of 64-bit integers implemented as a trie segmented into 8-bit chunks (bytes).
///
/// Each value is split into 8 bytes from most significant to least significant.
/// Nodes only get created as needed. Removal prunes empty branches.
#[derive(Default)]
pub struct SegmentedTrieSet {
    root: Node,
    len: usize,
}

struct Node {
    // 256-way branching per byte
    children: [Option<Box<Node>>; 256],
    terminal: bool,
}

impl fmt::Debug for SegmentedTrieSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl SegmentedTrieSet {
    pub fn new() -> Self { Self::default() }

    pub fn with_capacity(_cap: usize) -> Self {
        // Capacity hint isn't used in this implementation since branching is fixed-size.
        Self::default()
    }

    #[inline]
    pub fn len(&self) -> usize { self.len }

    #[inline]
    pub fn is_empty(&self) -> bool { self.len == 0 }

    pub fn clear(&mut self) {
        self.root = Node::default();
        self.len = 0;
    }

    /// Inserts a value. Returns true if the value was not present.
    pub fn insert(&mut self, value: u64) -> bool {
        let mut node = &mut self.root;
        for depth in (0..8).rev() { // 7 down to 0 (MSB first)
            let shift = depth * 8;
            let idx = ((value >> shift) & 0xFF) as usize;
            if node.children[idx].is_none() {
                node.children[idx] = Some(Box::new(Node::default()));
            }
            // Safety: just inserted or already present
            node = node.children[idx].as_mut().unwrap();
        }
        if node.terminal {
            false
        } else {
            node.terminal = true;
            self.len += 1;
            true
        }
    }

    /// Returns true if the value is present.
    pub fn contains(&self, value: &u64) -> bool {
        let mut node = &self.root;
        for depth in (0..8).rev() {
            let shift = depth * 8;
            let idx = ((*value >> shift) & 0xFF) as usize;
            match node.children[idx].as_deref() {
                Some(next) => node = next,
                None => return false,
            }
        }
        node.terminal
    }

    /// Removes a value. Returns true if the value was present.
    pub fn remove(&mut self, value: &u64) -> bool {
        if Self::remove_inner(&mut self.root, *value, 7) {
            self.len -= 1;
            true
        } else {
            false
        }
    }

    fn remove_inner(node: &mut Node, value: u64, depth: i32) -> bool {
        if depth < 0 {
            if node.terminal {
                node.terminal = false;
                true
            } else {
                false
            }
        } else {
            let shift = (depth as u32) * 8;
            let idx = ((value >> shift) & 0xFF) as usize;
            if let Some(child) = node.children[idx].as_mut() {
                let removed = Self::remove_inner(child, value, depth - 1);
                if removed {
                    // prune if child is now empty
                    if !child.terminal && child.children.iter().all(|c| c.is_none()) {
                        node.children[idx] = None;
                    }
                }
                removed
            } else {
                false
            }
        }
    }

    /// Returns an iterator over all values in the set (unordered).
    pub fn iter(&self) -> impl Iterator<Item = u64> + '_ {
        let mut out = Vec::with_capacity(self.len);
        self.collect_values(&self.root, 0, 7, &mut out);
        out.into_iter()
    }

    fn collect_values(&self, node: &Node, prefix: u64, depth: i32, out: &mut Vec<u64>) {
        if depth < 0 {
            if node.terminal { out.push(prefix); }
            return;
        }
        if node.terminal && depth == -1 { out.push(prefix); } // unreachable due to early return
        for (i, child) in node.children.iter().enumerate() {
            if let Some(child_node) = child.as_deref() {
                let value = (prefix << 8) | (i as u64);
                if depth == 0 {
                    if child_node.terminal { out.push(value); }
                } else {
                    self.collect_values(child_node, value, depth - 1, out);
                }
            }
        }
    }
}

impl Extend<u64> for SegmentedTrieSet {
    fn extend<T: IntoIterator<Item = u64>>(&mut self, iter: T) {
        for v in iter { let _ = self.insert(v); }
    }
}

impl std::iter::FromIterator<u64> for SegmentedTrieSet {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        let mut s = SegmentedTrieSet::new();
        s.extend(iter);
        s
    }
}

impl IntoIterator for SegmentedTrieSet {
    type Item = u64;
    type IntoIter = std::vec::IntoIter<u64>;
    fn into_iter(self) -> Self::IntoIter {
        // simple: collect then return vec iterator
        let mut out = Vec::with_capacity(self.len);
        self.collect_values(&self.root, 0, 7, &mut out);
        out.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use rand::rngs::StdRng;
    use rand::{SeedableRng, RngCore};

    #[test]
    fn basic_ops() {
        let mut s = SegmentedTrieSet::new();
        assert_eq!(s.len(), 0);
        assert!(s.insert(0));
        assert!(!s.insert(0));
        assert!(s.contains(&0));
        assert_eq!(s.len(), 1);

        assert!(s.insert(42));
        assert!(s.contains(&42));
        assert_eq!(s.len(), 2);

        assert!(s.remove(&0));
        assert!(!s.contains(&0));
        assert_eq!(s.len(), 1);

        assert!(!s.remove(&0));

        s.clear();
        assert!(s.is_empty());
    }

    #[test]
    fn iter_returns_all() {
        let mut s = SegmentedTrieSet::new();
        for v in [1u64, 2, 255, 256, u64::MAX] { s.insert(v); }
        let got: HashSet<u64> = s.iter().collect();
        let exp: HashSet<u64> = [1u64, 2, 255, 256, u64::MAX].into_iter().collect();
        assert_eq!(got, exp);
    }

    #[test]
    fn randomized_vs_hashset() {
        let mut rng = StdRng::seed_from_u64(12345);
        let mut tr = SegmentedTrieSet::new();
        let mut hs = HashSet::new();

        let n = 20_000;
        for _ in 0..n {
            let v = rng.next_u64();
            let a = tr.insert(v);
            let b = hs.insert(v);
            assert_eq!(a, b);
        }
        assert_eq!(tr.len(), hs.len());
        for _ in 0..n {
            let q = rng.next_u64();
            assert_eq!(tr.contains(&q), hs.contains(&q));
        }
        // remove about half
        for _ in 0..n/2 {
            let v = rng.next_u64();
            let a = tr.remove(&v);
            let b = hs.remove(&v);
            assert_eq!(a, b);
        }
        assert_eq!(tr.len(), hs.len());
        // final equality check via iteration
        let tr_set: HashSet<u64> = tr.iter().collect();
        assert_eq!(tr_set, hs);
    }
}

impl Default for Node {
    fn default() -> Self {
        Self {
            children: std::array::from_fn(|_| None),
            terminal: false,
        }
    }
}
