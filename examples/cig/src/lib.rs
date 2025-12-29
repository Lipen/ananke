//! # Canonical Interaction Graph (CIG)
//!
//! A semantic-structural canonical representation of Boolean functions based on
//! the intrinsic separability structure of variable interactions.
//!
//! ## Overview
//!
//! CIG provides a unique representation for Boolean functions by analyzing how
//! variables interact. Unlike BDDs (which depend on variable ordering) or SDDs
//! (which depend on vtree structure), CIG derives its structure entirely from
//! the function's intrinsic properties.
//!
//! ## Key Concepts
//!
//! - **Separability**: A function is separable over partition (A, B) if it can
//!   be expressed as g(A) ⊗ h(B) for some binary operator ⊗.
//!
//! - **Interaction Set**: A set of variables that interact irreducibly — no
//!   partition allows separation.
//!
//! - **Interaction Partition**: The unique maximal partition of variables into
//!   irreducible interaction blocks.
//!
//! - **Interaction Function**: The Boolean function that combines the outputs
//!   of child blocks at each internal node.
//!
//! ## Example
//!
//! ```rust
//! use cig::{CigBuilder, TruthTable, Var};
//!
//! // Create a simple function: (x₁ ⊕ x₂) ∧ x₃
//! let mut builder = CigBuilder::new();
//! let f = TruthTable::from_expr(3, |x| (x[0] ^ x[1]) & x[2]);
//!
//! let cig = builder.build(&f);
//!
//! // Analyze the interaction structure
//! println!("Interaction width: {}", cig.interaction_width());
//! println!("Depth: {}", cig.depth());
//! ```

pub mod analysis;
pub mod builder;
pub mod cig;
pub mod display;
pub mod interaction;
pub mod operations;
pub mod partition;
pub mod separability;
pub mod truth_table;
pub mod variable;

pub use analysis::{CigAnalysis, ComplexityClass};
pub use builder::CigBuilder;
pub use cig::{Cig, CigNode, CigNodeKind, UniqueTable};
pub use interaction::{InteractionFunction, Operator};
pub use partition::Partition;
pub use truth_table::TruthTable;
pub use variable::{Var, VarSet};

#[cfg(test)]
mod tests;
