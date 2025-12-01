use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use rand::{rngs::StdRng, SeedableRng, RngCore};
use std::collections::HashSet;

use radixset::SegmentedTrieSet;

fn bench_insert_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_random_u64");
    let n = 50_000;
    let seed = 42u64;

    group.bench_function("segmented_trie_set", |b| {
        b.iter_batched(
            || {
                let mut rng = StdRng::seed_from_u64(seed);
                (0..n).map(|_| rng.next_u64()).collect::<Vec<_>>()
            },
            |data| {
                let mut s = SegmentedTrieSet::new();
                for &v in &data { black_box(s.insert(v)); }
                black_box(s.len())
            },
            BatchSize::LargeInput,
        )
    });

    group.bench_function("hash_set", |b| {
        b.iter_batched(
            || {
                let mut rng = StdRng::seed_from_u64(seed);
                (0..n).map(|_| rng.next_u64()).collect::<Vec<_>>()
            },
            |data| {
                let mut s = HashSet::new();
                for &v in &data { black_box(s.insert(v)); }
                black_box(s.len())
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_contains_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("contains_random_u64");
    let n = 50_000;
    let q = 50_000;
    let seed = 24u64;

    group.bench_function("segmented_trie_set", |b| {
        b.iter_batched(
            || {
                let mut rng = StdRng::seed_from_u64(seed);
                let data = (0..n).map(|_| rng.next_u64()).collect::<Vec<_>>();
                let queries = (0..q).map(|_| rng.next_u64()).collect::<Vec<_>>();
                let mut s = SegmentedTrieSet::new();
                for &v in &data { s.insert(v); }
                (s, queries)
            },
            |(s, queries)| {
                let s = s; // move into bench closure
                for v in queries { black_box(s.contains(&v)); }
            },
            BatchSize::LargeInput,
        )
    });

    group.bench_function("hash_set", |b| {
        b.iter_batched(
            || {
                let mut rng = StdRng::seed_from_u64(seed);
                let data = (0..n).map(|_| rng.next_u64()).collect::<Vec<_>>();
                let queries = (0..q).map(|_| rng.next_u64()).collect::<Vec<_>>();
                let mut s = HashSet::new();
                for &v in &data { s.insert(v); }
                (s, queries)
            },
            |(s, queries)| {
                let s = s; // move into bench closure
                for v in queries { black_box(s.contains(&v)); }
            },
            BatchSize::LargeInput,
        )
    });

    group.finish();
}

criterion_group!(benches, bench_insert_random, bench_contains_random);
criterion_main!(benches);
