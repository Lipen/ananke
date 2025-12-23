//! Incremental Decision Diagrams for Evolving Symbolic Systems
//!
//! This library provides incremental algorithms for decision diagram-based
//! verification and synthesis. Instead of recomputing from scratch when a
//! system changes, incremental algorithms reuse previous results where possible.
//!
//! # Overview
//!
//! The library provides:
//!
//! - **Delta representation**: A formal notion of semantic change
//! - **Incremental reachability**: Update reachability when transitions change
//! - **Incremental safety verification**: Re-verify properties efficiently
//! - **Incremental synthesis**: Maintain solution spaces under constraints
//!
//! # Quick Start
//!
//! ```
//! use std::rc::Rc;
//! use ananke_bdd::bdd::Bdd;
//! use ananke_bdd::types::Var;
//! use incremental_dd::synthesis::IncrementalConstraintSynthesizer;
//! use incremental_dd::traits::IncrementalSynthesizer;
//!
//! let bdd = Rc::new(Bdd::default());
//! let vars = vec![Var::new(1), Var::new(2), Var::new(3)];
//!
//! // Create a synthesizer
//! let mut synth = IncrementalConstraintSynthesizer::new(bdd.clone(), vars);
//!
//! // Add constraints incrementally
//! let x1 = bdd.mk_var(Var::new(1));
//! synth.add_constraint(x1);  // x1 must be true
//!
//! // Check satisfiability
//! assert!(synth.is_sat());
//! ```
//!
//! # Modules
//!
//! - [`mod@delta`]: Delta representation and operations
//! - [`mod@traits`]: Trait definitions for incremental objects
//! - [`mod@incremental_ts`]: Incremental transition systems
//! - [`mod@safety`]: Incremental safety verification
//! - [`mod@synthesis`]: Incremental constraint-based synthesis
//! - [`mod@metrics`]: Performance metrics collection

pub mod delta;
pub mod incremental_ts;
pub mod metrics;
pub mod safety;
pub mod synthesis;
pub mod traits;

// Re-exports for convenience
pub use delta::{Delta, DeltaEffect, DeltaError, SystemDelta};
pub use incremental_ts::{IncrementalReachabilityFixpoint, IncrementalTransSystem};
pub use metrics::{IncrementalMetricsData, MetricsCollector, MetricsTimer};
pub use safety::IncrementalSafetyChecker;
pub use synthesis::{IncrementalConstraintSynthesizer, SynthesizerBuilder};
pub use traits::{
    ConstraintEffect, FixpointUpdate, IncrementalFixpoint, IncrementalMetrics, IncrementalObject, IncrementalSynthesizer,
    IncrementalTransitionSystem, IncrementalVerificationResult, IncrementalVerifier, VerificationResult,
};
