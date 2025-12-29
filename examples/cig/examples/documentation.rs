//! Examples from CIG.md documentation
//!
//! Implements Examples 3.10, 4.8, 4.9, 4.10, 4.11 from the specification.
//! Run with: cargo run --example documentation

use cig::{CigBuilder, Partition, TruthTable, Var, VarSet};

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("                CIG Documentation Examples");
    println!("═══════════════════════════════════════════════════════════\n");

    let mut builder = CigBuilder::new();

    // Example 3.10
    println!("═══ Example 3.10: Interaction Partition");
    println!("Function: f = (x1 AND x2) XOR x3\n");

    let f_3_10 = TruthTable::from_expr(3, |x| (x[0] && x[1]) ^ x[2]);
    let cig = builder.build(&f_3_10);
    println!("{0:?}\n{0}", cig);

    println!("Analysis:");
    let partition = cig.extract_partition();
    println!("  Partition: {}", partition);
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Assert the partition structure
    let expected = Partition::from_blocks(vec![VarSet::from_iter([Var(1), Var(2)]), VarSet::from_iter([Var(3)])]);
    assert_eq!(partition, expected);

    // Example 4.8
    println!("═══ Example 4.8: Parity Function");
    println!("Function: f = x1 XOR x2 XOR x3 XOR x4 XOR x5\n");

    let parity_5 = TruthTable::from_expr(5, |x| x.iter().fold(false, |acc, &b| acc ^ b));
    let cig = builder.build(&parity_5);
    println!("{0:?}\n{0}", cig);

    println!("Analysis:");
    let partition = cig.extract_partition();
    println!("  Partition: {}", partition);
    println!("  N-ary XOR: all variables are direct children (flat structure)");
    println!("  Canonical form ensures unique representation");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Assert the partition structure - n-ary flattening produces individual blocks
    let expected = Partition::from_blocks(vec![
        VarSet::from_iter([Var(1)]),
        VarSet::from_iter([Var(2)]),
        VarSet::from_iter([Var(3)]),
        VarSet::from_iter([Var(4)]),
        VarSet::from_iter([Var(5)]),
    ]);
    assert_eq!(partition, expected);

    // Example 4.9
    println!("═══ Example 4.9: Majority Function");
    println!("Function: f = MAJ3(x1, x2, x3)");
    println!("          = (x1 AND x2) OR (x2 AND x3) OR (x1 AND x3)\n");

    let maj_3 = TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2]));
    let cig = builder.build(&maj_3);
    println!("{0:?}\n{0}", cig);

    println!("Analysis:");
    let partition = cig.extract_partition();
    println!("  Partition: {}", partition);
    println!("  All variables interact irreducibly");
    println!("  NOT separable (all appear as direct children)");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Assert the partition structure - all as separate children at root
    let expected = Partition::from_blocks(vec![
        VarSet::from_iter([Var(1)]),
        VarSet::from_iter([Var(2)]),
        VarSet::from_iter([Var(3)]),
    ]);
    assert_eq!(partition, expected);

    // Example 4.10
    println!("═══ Example 4.10: Multiplexer");
    println!("Function: f = MUX(s, x, y) = (NOT s AND x) OR (s AND y)\n");

    let mux = TruthTable::from_expr(3, |x| (!x[0] && x[1]) || (x[0] && x[2]));
    let cig = builder.build(&mux);
    println!("{0:?}\n{0}", cig);

    println!("Analysis:");
    let partition = cig.extract_partition();
    println!("  Partition: {}", partition);
    println!("  All variables interact");
    println!("  Cannot separate over any 2-1 partition");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Assert the partition structure - all as separate children at root
    let expected = Partition::from_blocks(vec![
        VarSet::from_iter([Var(1)]),
        VarSet::from_iter([Var(2)]),
        VarSet::from_iter([Var(3)]),
    ]);
    assert_eq!(partition, expected);

    // Example 4.11
    println!("═══ Example 4.11: Composed Function");
    println!("Function: f = (x1 XOR x2) AND (x3 OR x4)\n");

    let composed = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] || x[3]));
    let cig = builder.build(&composed);
    println!("{0:?}\n{0}", cig);

    println!("Analysis:");
    let partition = cig.extract_partition();
    println!("  Partition: {}", partition);
    println!("  Separable at root via AND");
    println!("  CIG nodes: {}, depth: {}\n", cig.size(), cig.depth());

    // Assert the partition structure
    let expected = Partition::from_blocks(vec![VarSet::from_iter([Var(1), Var(2)]), VarSet::from_iter([Var(3), Var(4)])]);
    assert_eq!(partition, expected);

    println!("───────────────────────────────────────────────────────────");
    println!("                            SUMMARY");
    println!("───────────────────────────────────────────────────────────\n");
    println!("  Example 3.10: Decomposable structure");
    println!("  Example 4.8: Fully separable (parity)");
    println!("  Example 4.9: Fully irreducible (majority)");
    println!("  Example 4.10: Fully irreducible (multiplexer)");
    println!("  Example 4.11: Hierarchical decomposition");
    println!("\n═══════════════════════════════════════════════════════════");
}
