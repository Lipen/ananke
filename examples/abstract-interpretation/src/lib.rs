//! # Abstract Interpretation: A Case Study
//!
//! This crate serves as a comprehensive case study and framework for building static analysis tools using
//! **Abstract Interpretation**. It demonstrates how to verify program properties --- such as safety,
//! termination, and correctness --- by mathematically approximating program behavior.
//!
//! ## Core Concept
//!
//! Unlike standard testing (which checks one execution path) or fuzzing (which checks many),
//! **Abstract Interpretation checks all possible execution paths simultaneously.**
//!
//! Instead of executing a program with concrete values (e.g., `let x = 5`), we execute it with
//! **Abstract Values** (e.g., `let x = Sign::Positive`).
//!
//! ### Why BDDs?
//!
//! Traditional analyzers often lose precision at merge points (e.g., after an `if/else`) because they
//! must merge conflicting states into a single approximation.
//!
//! - **Without BDDs**: "x is roughly between 0 and 10."
//! - **With BDDs**: "x is 5 IF flag_a is true, OR x is 9 IF flag_b is false."
//!
//! BDDs provide **path sensitivity** efficiently, allowing us to track complex boolean relationships
//! without exponential memory growth.
//!
//! ## Abstract Execution
//!
//! By choosing different **Abstract Domains**, we can trade precision for speed.
//!
//! | Code | Concrete Execution | Interval Domain | Sign Domain |
//! |------|--------------------|-----------------|-------------|
//! | `let x = 5;` | `x = 5` | `x ∈ [5, 5]` | `x` is `Pos` |
//! | `let y = x - 10;` | `y = -5` | `y ∈ [-5, -5]` | `y` is `Neg` |
//! | `if y >= 0` | `false` (branch not taken) | `[-5, -5] >= 0` is **False** | `Neg >= 0` is **False** |
//!
//! ## Available Domains
//!
//! This framework provides a rich set of domains to track different aspects of program state.
//!
//! ### 1. Numeric Domains
//! - **[`IntervalDomain`]**: Tracks ranges (e.g., `x ∈ [0, 100]`). Ideal for array bounds checks.
//! - **[`SignDomain`]**: Tracks signs (`+`, `-`, `0`). Efficient for division-by-zero checks.
//! - **[`CongruenceDomain`]**: Tracks stride and offset (e.g., `x % 4 == 1`). Useful for memory alignment.
//! - **[`ConstantDomain`]**: Tracks constant values (e.g., `x = 42`).
//!
//! ### 2. Control Flow & BDDs
//! - **[`BddControlDomain`]**: Uses BDDs to track boolean flags and control flow history.
//!   - *Example*: "If `error_flag` is true, then `is_valid` must be false."
//! - **[`AutomataDomain`]**: Verifies state machine transitions (e.g., ensuring `open()` is called before `read()`).
//!
//! ### 3. Memory & Pointers
//! - **[`PointsToDomain`]**: Uses BDDs to efficiently track sets of memory locations a pointer might target (Alias Analysis).
//!
//! ### 4. String Analysis
//! - **[`StringPrefixDomain`]**: Tracks string prefixes (e.g., "Starts with 'https://'").
//! - **[`StringLengthDomain`]**: Tracks string lengths (e.g., "Length is at most 255").
//!
//! ## Theoretical Foundations
//!
//! Abstract Interpretation is based on **Lattice Theory**.
//! An Abstract Domain is defined as a lattice `⟨D, ⊑, ⊥, ⊤, ⊔, ⊓⟩`:
//!
//! - **`D` (Domain)**: The set of all possible abstract states.
//! - **`⊑` (Partial Order)**: The precision relation. `x ⊑ y` means `x` is more precise (contains fewer concrete behaviors) than `y`.
//! - **`⊥` (Bottom)**: The empty state (unreachable code).
//! - **`⊤` (Top)**: The unknown state (any behavior is possible).
//! - **`⊔` (Join)**: The least upper bound. Used to merge control flow paths.
//! - **`⊓` (Meet)**: The greatest lower bound. Used to refine states (e.g., at conditionals).
//!
//! ### Fixpoint Computation
//!
//! Analyzing loops is the hardest part of static analysis. We need to find an **invariant** --- a state that holds true before and after the loop body, regardless of how many times the loop executes.
//!
//! Mathematically, for a loop transfer function `F`, we seek the **Least Fixed Point (LFP)**, denoted as `lfp(F)`.
//! This is the smallest state `X` such that `F(X) = X`.
//!
//! The **[`FixpointEngine`]** in this crate automates this process. It iteratively applies the transfer function until the state stabilizes (converges).
//!
//! ### Widening (∇) & Narrowing (△)
//!
//! For infinite height lattices (like Intervals), standard iteration might not converge in finite time (e.g., `[0, 1], [0, 2], [0, 3]...`).
//!
//! 1. **Widening (∇)**: Accelerates convergence by over-approximating. If a value grows in consecutive iterations, widening jumps to a limit (e.g., `+∞`).
//!   - *Example*: If we see `x` go from `[0, 1]` to `[0, 2]`, we might guess `[0, +∞]` immediately.
//! 2. **Narrowing (△)**: Recovers precision lost by widening. Once a post-fixpoint is found (which is safe but imprecise), we iterate downwards to find a tighter bound.
//!   - *Example*: After guessing `[0, +∞]`, we check the loop condition `x < 10`. The narrowing step refines the state to `[0, 10]`.
//!
//! ## Example: Analyzing a Simple Program
//!
//! ```rust
//! use abstract_interpretation::*;
//!
//! // 1. Define the domain (Intervals)
//! let domain = IntervalDomain;
//!
//! // 2. Define the program state (x = 0)
//! let state = domain.interval("x", 0, 0);
//! println!("Initial state: {:?}", state); // x ∈ [0, 0]
//!
//! // 3. Analyze an assignment: x = x + 5
//! let expr = NumExpr::Add(
//!     Box::new(NumExpr::Var("x".to_string())),
//!     Box::new(NumExpr::Const(5))
//! );
//!
//! // Update the state with the new value
//! let next_state = domain.assign(&state, "x", &expr);
//!
//! // 4. Verify the result
//! let bounds = domain.get_bounds(&next_state, "x").unwrap();
//! assert_eq!(bounds, (5, 5));
//! println!("After assignment: x ∈ {:?}", bounds);
//! ```
//!
//! ## Further Reading
//!
//! - **`examples/realistic_programs.rs`**: Demonstrates complex scenarios combining multiple domains.
//! - **`examples/pointsto_example.rs`**: A deep dive into BDD-based pointer analysis.
//! - **Cousot & Cousot (1977)**: The foundational paper on Abstract Interpretation.
//!
//! For detailed documentation, see individual module pages.

pub mod automata;
pub mod bdd_control;
pub mod congruence;
pub mod constant;
pub mod domain;
pub mod expr;
pub mod fixpoint;
pub mod generic_product;
pub mod interval;
pub mod numeric;
pub mod pointsto;
pub mod product;
pub mod sdd_control;
pub mod sign;
pub mod string_domain;
pub mod transfer;
pub mod type_domain;

// Re-exports for convenience
pub use automata::{AutomataDomain, CharClass, Predicate, SymbolicDFA, SymbolicNFA};
pub use bdd_control::{BddControlDomain, ControlSensitiveElement, ControlSensitiveProduct, ControlState};
pub use congruence::{Congruence, CongruenceDomain};
pub use constant::{ConstValue, ConstantDomain, ConstantElement};
pub use domain::AbstractDomain;
pub use expr::{NumExpr, NumPred, Stmt};
pub use fixpoint::FixpointEngine;
pub use interval::{Bound, Interval, IntervalDomain, IntervalElement};
pub use numeric::NumericDomain;
pub use pointsto::{Location, LocationMap, PointsToDomain, PointsToElement};
pub use product::{ProductDomain, ProductElement};
pub use sdd_control::{SddControlDomain, SddControlState};
pub use sign::{Sign, SignDomain, SignElement};
pub use string_domain::{
    CharacterSet, CharacterSetDomain, StringConst, StringConstantDomain, StringInclusionDomain, StringLengthDomain, StringPrefixDomain,
    StringSuffixDomain,
};
pub use transfer::{NumericTransferFunction, TransferFunction};
pub use type_domain::{Type, TypeDomain, TypeSet};
