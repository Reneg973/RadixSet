pub mod segmented_trie_set;
pub mod segmented_trie_string_set;
pub mod segmented_trie_string_set_flat;

/// Unique identifier type for trie terminal nodes.
///
/// Holds the raw heap address of the node as returned by addr_id_of.
/// This is only valid while the corresponding node exists.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct TrieSetId {
    pub addr: usize,
}

pub use segmented_trie_set::SegmentedTrieSet;
pub use segmented_trie_string_set::SegmentedTrieStringSet;
pub use segmented_trie_string_set_flat::SegmentedTrieStringSetFlat;
