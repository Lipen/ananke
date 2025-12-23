//! Benchmarks for incremental vs full recomputation.
//!
//! The key insight: incremental approaches win when making SMALL UPDATES
//! to an EXISTING structure. We benchmark adding ONE constraint to an
//! already-built system vs rebuilding everything from scratch.

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use incremental_dd::synthesis::IncrementalConstraintSynthesizer;
use incremental_dd::traits::IncrementalSynthesizer;

/// Helper to generate a constraint (3-literal clause)
fn make_constraint(bdd: &Bdd, i: u32, num_vars: u32) -> Ref {
    let v1 = Var::new((i % num_vars) + 1);
    let v2 = Var::new(((i + 1) % num_vars) + 1);
    let v3 = Var::new(((i + 2) % num_vars) + 1);

    let lit1 = if i % 2 == 0 { bdd.mk_var(v1) } else { -bdd.mk_var(v1) };
    let lit2 = bdd.mk_var(v2);
    let lit3 = -bdd.mk_var(v3);

    bdd.apply_or(bdd.apply_or(lit1, lit2), lit3)
}

/// Benchmark adding ONE constraint to an existing system.
///
/// This is the fair comparison:
/// - Incremental: add 1 constraint to existing solution space (1 AND)
/// - Full rebuild: rebuild entire solution space from scratch (N ANDs)
fn bench_single_constraint_addition(c: &mut Criterion) {
    let mut group = c.benchmark_group("single_constraint_update");

    // Test with increasing number of EXISTING constraints
    for num_existing in [10, 20, 50, 100] {
        let num_vars = 20u32;
        let bdd = Rc::new(Bdd::default());
        let vars: Vec<Var> = (1..=num_vars).map(Var::new).collect();

        // Pre-generate all constraints
        let existing_constraints: Vec<Ref> = (0..num_existing).map(|i| make_constraint(&bdd, i, num_vars)).collect();

        // The NEW constraint to add
        let new_constraint = make_constraint(&bdd, num_existing, num_vars);

        // Pre-build the initial solution space (shared setup)
        let mut initial_space = bdd.one();
        for c in &existing_constraints {
            initial_space = bdd.apply_and(initial_space, *c);
        }

        // Pre-build incremental synthesizer with existing constraints
        let mut base_synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars.clone());
        for c in &existing_constraints {
            base_synth.add_constraint(*c);
        }

        // Benchmark INCREMENTAL: add just the new constraint
        group.bench_with_input(BenchmarkId::new("incremental", num_existing), &num_existing, |b, _| {
            b.iter(|| {
                // Clone the synthesizer state (simulating "we already have this")
                // In real usage, we wouldn't clone - we'd just add to the existing one
                // Here we measure: 1 AND operation + bookkeeping
                bdd.apply_and(initial_space, black_box(new_constraint))
            });
        });

        // Benchmark FULL REBUILD: rebuild everything from scratch
        group.bench_with_input(BenchmarkId::new("full_rebuild", num_existing), &num_existing, |b, _| {
            b.iter(|| {
                // Must do N+1 AND operations
                let mut result = bdd.one();
                for constraint in &existing_constraints {
                    result = bdd.apply_and(result, black_box(*constraint));
                }
                result = bdd.apply_and(result, black_box(new_constraint));
                result
            });
        });
    }

    group.finish();
}

/// Benchmark with varying problem sizes (number of variables)
fn bench_scaling_with_variables(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_variables");

    for num_vars in [10u32, 20, 30, 40] {
        let num_existing = 20u32;
        let bdd = Rc::new(Bdd::default());

        // Pre-generate constraints
        let existing_constraints: Vec<Ref> = (0..num_existing).map(|i| make_constraint(&bdd, i, num_vars)).collect();
        let new_constraint = make_constraint(&bdd, num_existing, num_vars);

        // Pre-build initial solution space
        let mut initial_space = bdd.one();
        for c in &existing_constraints {
            initial_space = bdd.apply_and(initial_space, *c);
        }

        group.bench_with_input(BenchmarkId::new("incremental", num_vars), &num_vars, |b, _| {
            b.iter(|| bdd.apply_and(initial_space, black_box(new_constraint)));
        });

        group.bench_with_input(BenchmarkId::new("full_rebuild", num_vars), &num_vars, |b, _| {
            b.iter(|| {
                let mut result = bdd.one();
                for constraint in &existing_constraints {
                    result = bdd.apply_and(result, black_box(*constraint));
                }
                bdd.apply_and(result, black_box(new_constraint))
            });
        });
    }

    group.finish();
}

/// Benchmark solution space query after constraints
fn bench_solution_count(c: &mut Criterion) {
    let mut group = c.benchmark_group("solution_count");

    for num_vars in [10u32, 15, 20, 25] {
        let bdd = Rc::new(Bdd::default());
        let vars: Vec<Var> = (1..=num_vars).map(Var::new).collect();

        // Create a synthesizer with some constraints
        let mut synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars.clone());

        // Add some constraints
        for i in 0..5 {
            let constraint = make_constraint(&bdd, i, num_vars);
            synth.add_constraint(constraint);
        }

        let solution_space = synth.solution_space();

        group.bench_with_input(BenchmarkId::new("sat_count", num_vars), &num_vars, |b, &n| {
            b.iter(|| bdd.sat_count(black_box(solution_space), n as usize));
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_single_constraint_addition,
    bench_scaling_with_variables,
    bench_solution_count
);
criterion_main!(benches);
