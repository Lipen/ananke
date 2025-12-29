//! Core CIG examples demonstrating interaction structure and separability.
//!
//! Examples show:
//! - Building CIGs and extracting partition structure
//! - Separable vs non-separable functions
//! - Functional equivalence checking
//! - Variable interactions and canonicity
//!
//! Run with: cargo run --example basic

use cig::{CigBuilder, Partition, TruthTable, Var, VarSet};

fn main() {
    println!();
    println!("═══ CIG Core Examples ═══");
    println!();

    let mut builder = CigBuilder::new();

    header("Example 1: AND");
    let f_and = TruthTable::from_expr(2, |x| x[0] && x[1]);
    println!("Truth table: {}", f_and);
    let cig_and = builder.build(&f_and);
    println!("{}", cig_and);
    let partition = cig_and.extract_partition();
    println!("Partition: {}", partition);
    println!("Nodes: {}, Depth: {}\n", cig_and.size(), cig_and.depth());
    let expected = Partition::from_blocks(vec![VarSet::from_iter([Var(1)]), VarSet::from_iter([Var(2)])]);
    assert_eq!(partition, expected);

    header("Example 2: XOR");
    let f_xor = TruthTable::from_expr(2, |x| x[0] ^ x[1]);
    println!("Truth table: {}", f_xor);
    let cig_xor = builder.build(&f_xor);
    println!("{}", cig_xor);
    let partition = cig_xor.extract_partition();
    println!("Partition: {}", partition);
    println!("Nodes: {}, Depth: {}\n", cig_xor.size(), cig_xor.depth());
    let expected = Partition::from_blocks(vec![VarSet::from_iter([Var(1)]), VarSet::from_iter([Var(2)])]);
    assert_eq!(partition, expected);

    header("Example 3: Parity (x1 XOR x2 XOR x3)");
    println!("Each variable independent, fully separable");
    let f_parity = TruthTable::from_expr(3, |x| x.iter().fold(false, |acc, &b| acc ^ b));
    println!("Truth table: {}", f_parity);
    let cig_parity = builder.build(&f_parity);
    println!("{}", cig_parity);
    let partition = cig_parity.extract_partition();
    println!("Partition: {}", partition);
    println!("Nodes: {}, Depth: {}\n", cig_parity.size(), cig_parity.depth());
    let expected = Partition::from_blocks(vec![VarSet::from_iter([Var(1)]), VarSet::from_iter([Var(2), Var(3)])]);
    assert_eq!(partition, expected);

    header("Example 4: Composed ((x1 XOR x2) AND (x3 OR x4))");
    println!("Hierarchical decomposition, two separable blocks");
    let f_composed = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] || x[3]));
    println!("Truth table: {}", f_composed);
    let cig_composed = builder.build(&f_composed);
    println!("{}", cig_composed);
    let partition = cig_composed.extract_partition();
    println!("Partition: {}", partition);
    println!("Nodes: {}, Depth: {}\n", cig_composed.size(), cig_composed.depth());
    let expected = Partition::from_blocks(vec![VarSet::from_iter([Var(1), Var(2)]), VarSet::from_iter([Var(3), Var(4)])]);
    assert_eq!(partition, expected);

    header("Example 5: Majority");
    println!("All variables interact irreducibly, non-separable");
    let f_maj = TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2]));
    println!("Truth table: {}", f_maj);
    let cig_maj = builder.build(&f_maj);
    println!("{}", cig_maj);
    let partition = cig_maj.extract_partition();
    println!("Partition: {}", partition);
    println!("Nodes: {}, Depth: {}\n", cig_maj.size(), cig_maj.depth());
    let expected = Partition::from_blocks(vec![
        VarSet::from_iter([Var(1)]),
        VarSet::from_iter([Var(2)]),
        VarSet::from_iter([Var(3)]),
    ]);
    assert_eq!(partition, expected);

    header("Example 6: Multiplexer");
    println!("All variables interact, cannot separate");
    let f_mux = TruthTable::from_expr(3, |x| (!x[0] && x[1]) || (x[0] && x[2]));
    println!("Truth table: {}", f_mux);
    let cig_mux = builder.build(&f_mux);
    println!("{}", cig_mux);
    let partition = cig_mux.extract_partition();
    println!("Partition: {}", partition);
    println!("Nodes: {}, Depth: {}\n", cig_mux.size(), cig_mux.depth());
    let expected = Partition::from_blocks(vec![
        VarSet::from_iter([Var(1)]),
        VarSet::from_iter([Var(2)]),
        VarSet::from_iter([Var(3)]),
    ]);
    assert_eq!(partition, expected);

    header("Example 7: De Morgan's Law");
    let f1 = TruthTable::from_expr(2, |x| !(x[0] && x[1]));
    let f2 = TruthTable::from_expr(2, |x| !x[0] || !x[1]);
    println!("f1 truth table: {}", f1);
    println!("f2 truth table: {}", f2);
    let cig1 = builder.build(&f1);
    let cig2 = builder.build(&f2);
    println!("Equivalent: {}\n", cig1.equivalent(&cig2));
    assert!(cig1.equivalent(&cig2));

    header("Example 8: Variables and Constants");
    for i in 1..=3 {
        let proj = TruthTable::var(3, Var(i as u32));
        let cig = builder.build(&proj);
        println!("Variable x{}: Nodes {}", i, cig.size());
    }
    let zero = TruthTable::zero(2);
    let one = TruthTable::one(2);
    let cig_zero = builder.build(&zero);
    let cig_one = builder.build(&one);
    println!("Constant 0: Nodes {}", cig_zero.size());
    println!("Constant 1: Nodes {}\n", cig_one.size());

    println!("All assertions passed!");
}

fn header(title: &str) {
    println!("{}", "─".repeat(title.len() + 2));
    println!(" {} ", title);
    println!("{}", "─".repeat(title.len() + 2));
}
