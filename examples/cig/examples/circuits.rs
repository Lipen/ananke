//! CIG Examples: Realistic circuits demonstrating complexity patterns
//!
//! Run with: cargo run --example circuits

use cig::{CigBuilder, TruthTable};

fn main() {
    println!("═══════════════════════════════════════════════════════════");
    println!("                  CIG Circuit Examples");
    println!("═══════════════════════════════════════════════════════════\n");

    let mut builder = CigBuilder::new();

    // SECTION 1: Easy (separable) circuits
    println!("─── EASY CIRCUITS (Separable) ───\n");

    // Parity
    println!("Parity-4: x1 XOR x2 XOR x3 XOR x4");
    let parity_4 = TruthTable::from_expr(4, |x| x[0] ^ x[1] ^ x[2] ^ x[3]);
    let cig = builder.build(&parity_4);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: All variables independent");
    println!("  BDD width: O(1) with any ordering\n");

    // Full adder sum
    println!("Full Adder Sum: a XOR b XOR c_in");
    let fa_sum = TruthTable::from_expr(3, |x| x[0] ^ x[1] ^ x[2]);
    let cig = builder.build(&fa_sum);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: Fully separable");
    println!("  BDD width: O(1)\n");

    // SECTION 2: Mixed (structured) circuits
    println!("─── MIXED CIRCUITS (Structured) ───\n");

    // Full adder carry
    println!("Full Adder Carry: (a AND b) OR (c_in AND (a XOR b))");
    let fa_carry = TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[2] && (x[0] ^ x[1])));
    let cig = builder.build(&fa_carry);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: Carry chain, mixed interactions");
    println!("  BDD width: Polynomial\n");

    // 2x2 multiplier product bit 1
    println!("2-bit Multiplier (a0 AND b1) XOR (a1 AND b0)");
    let mult = TruthTable::from_expr(4, |x| (x[0] && x[3]) ^ (x[1] && x[2]));
    let cig = builder.build(&mult);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: Partial products");
    println!("  BDD width: Manageable\n");

    // Mixed decomposable
    println!("Mixed: (x1 XOR x2) AND (x3 OR x4)");
    let mixed = TruthTable::from_expr(4, |x| (x[0] ^ x[1]) && (x[2] || x[3]));
    let cig = builder.build(&mixed);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: Hierarchical decomposition");
    println!("  Partition: {{x1, x2}}, {{x3, x4}}\n");

    // SECTION 3: Hard (irreducible) circuits
    println!("─── HARD CIRCUITS (Irreducible) ───\n");

    // Multiplexer
    println!("2:1 Multiplexer: (NOT s AND a) OR (s AND b)");
    let mux = TruthTable::from_expr(3, |x| (!x[0] && x[1]) || (x[0] && x[2]));
    let cig = builder.build(&mux);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: All variables interact");
    println!("  BDD width: At least 2^(3-1) = 4\n");

    // Majority-5
    println!("Majority-5: True if 3+ of 5 inputs true");
    let maj_5 = TruthTable::from_expr(5, |x| x.iter().filter(|&&b| b).count() >= 3);
    let cig = builder.build(&maj_5);
    println!("  CIG: {} nodes, depth: {}, width: {}", cig.size(), cig.depth(), cig.interaction_width());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!("  Structure: Symmetric but irreducible");
    println!("  BDD width: Exponential regardless of ordering\n");

    // SECTION 4: Complexity analysis
    println!("─── COMPLEXITY ANALYSIS ───\n");

    println!("Width vs Representation Size:");
    println!();

    // ω = 1
    let x1 = TruthTable::from_expr(1, |x| x[0]);
    let cig = builder.build(&x1);
    println!("  (single variable x1)");
    println!("  width: {}", cig.interaction_width());
    println!("  nodes: {}", cig.size());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!();

    // ω = 2
    let or2 = TruthTable::from_expr(2, |x| x[0] || x[1]);
    let cig = builder.build(&or2);
    assert_eq!(cig.interaction_width(), 2);
    println!("  (x1 OR x2)");
    println!("  width: {}", cig.interaction_width());
    println!("  nodes: {}", cig.size());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!();

    // ω = 3
    let maj3 = TruthTable::from_expr(3, |x| (x[0] && x[1]) || (x[1] && x[2]) || (x[0] && x[2]));
    let cig = builder.build(&maj3);
    assert_eq!(cig.interaction_width(), 3);
    println!("  (Majority-3)");
    println!("  width: {}", cig.interaction_width());
    println!("  nodes: {}", cig.size());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!();

    // ω = 4
    let maj4 = TruthTable::from_expr(4, |x| x.iter().filter(|&&b| b).count() >= 2);
    let cig = builder.build(&maj4);
    assert_eq!(cig.interaction_width(), 4);
    println!("  (Majority-4)");
    println!("  width: {}", cig.interaction_width());
    println!("  nodes: {}", cig.size());
    for line in cig.to_string().lines() {
        println!("  {}", line);
    }
    println!();

    println!("─── KEY INSIGHTS ───");
    println!();
    println!("  1. Separability is crucial:");
    println!("     - Parity functions: O(n) CIG, easy representation");
    println!("     - All variables independent -> polynomial complexity");
    println!();
    println!("  2. Multiplexers are fundamentally hard:");
    println!("     - Cannot separate select from data");
    println!("     - CIG proves this is not an ordering artifact");
    println!();
    println!("  3. Majority is symmetric but irreducible:");
    println!("     - All variables must interact");
    println!("     - Hard regardless of representation choice");
    println!();
    println!("  4. Structure determines complexity:");
    println!("     - Not just gate count");
    println!("     - CIG reveals variable interactions");
    println!("     - Provides lower bounds on BDD width");
    println!("\n═══════════════════════════════════════════════════════════");
}
