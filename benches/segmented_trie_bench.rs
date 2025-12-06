use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand::{rng, Rng};
use std::collections::HashSet;
use std::hint::black_box;
use radixset::segmented_trie_string_set_flat::NodeId;
use radixset::SegmentedTrieSet;

fn random_string_custom(len: usize) -> String {
    const CHARSET: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
    let mut rng = rng();
    (0..len)
      .map(|_| {
          let idx = rng.random_range(0..CHARSET.len());
          CHARSET[idx] as char
      })
      .collect()
}

fn bench_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_random_str");
    let n = 20_000;

    let bench_data = (0..n).map(|_| random_string_custom(12)).collect::<Vec<_>>();
    let mut keys: Vec<NodeId> = Vec::with_capacity(n);
    let mut ss = SegmentedTrieSet::<'.'>::new();
    let mut hs = HashSet::new();

    group.bench_function("segmented_trie_set_insert", |b| {
        b.iter_batched(
            || {
                &bench_data
            },
            |data| {
                for v in data {
                    black_box(match ss.insert(v.as_str()) {
                        Ok(node_id) => keys.push(node_id),
                        Err(_) => {}
                    })
                }
            },
            BatchSize::LargeInput,
        )
    });

    group.bench_function("hash_set_insert", |b| {
        b.iter_batched(
            || {
                &bench_data
            },
            |data| {
                for v in data { let _ = black_box(hs.insert(v)); }
                black_box(hs.len())
            },
            BatchSize::LargeInput,
        )
    });

    group.bench_function("segmented_trie_set_lookup", |b| {
        b.iter_batched(
            || {
                &keys
            },
            |keys| {
                for v in keys { let _ = black_box(ss.get_by_id(v.clone())); }
            },
            BatchSize::LargeInput,
        )
    });

    group.bench_function("hash_set_lookup", |b| {
        b.iter_batched(
            || {
                &bench_data
            },
            |data| {
                for v in data { let _ = black_box(hs.contains(v)); }
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}


criterion_group!(benches, bench_random);
criterion_main!(benches);
