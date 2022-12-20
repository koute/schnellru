use criterion::{black_box, criterion_group, criterion_main, Criterion};
use schnellru::*;

fn lru_benchmarks(c: &mut Criterion) {
    c.bench_function("insert million elements with half million cap (schnellru)", |b| {
        b.iter(|| {
            let mut map = LruMap::new(ByLength::new(500000));
            for n in 0..1000000 {
                map.insert(n, n);
            }

            assert_eq!(map.len(), 500000);
            black_box(map)
        })
    });

    c.bench_function("insert million elements with half million cap (lru)", |b| {
        b.iter(|| {
            let mut map = lru::LruCache::new(std::num::NonZeroUsize::new(500000).unwrap());
            for n in 0..1000000 {
                map.push(n, n);
            }

            assert_eq!(map.len(), 500000);
            black_box(map)
        })
    });

    c.bench_function("insert million elements (schnellru)", |b| {
        b.iter(|| {
            let mut map = LruMap::new(UnlimitedCompact);
            for n in 0..1000000 {
                map.insert(n, n);
            }

            assert_eq!(map.len(), 1000000);
            black_box(map)
        })
    });

    c.bench_function("insert million elements (indexmap)", |b| {
        b.iter(|| {
            let mut map = indexmap::IndexMap::new();
            for n in 0..1000000 {
                map.insert(n, n);
            }

            assert_eq!(map.len(), 1000000);
            black_box(map)
        })
    });
}

criterion_group!(benches, lru_benchmarks);
criterion_main!(benches);
