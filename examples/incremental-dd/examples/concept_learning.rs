//! Concept Learning via Incremental Synthesis
//!
//! This example demonstrates using incremental constraint synthesis for
//! **concept learning** — finding a boolean formula that correctly classifies
//! a set of positive and negative examples.
//!
//! ## The Problem
//!
//! Given:
//! - Positive examples: assignments that should satisfy the target concept
//! - Negative examples: assignments that should NOT satisfy the target concept
//!
//! Find: A boolean formula F such that:
//! - F(x) = true for all positive examples x
//! - F(x) = false for all negative examples x
//!
//! ## The Approach
//!
//! We maintain a concept as a BDD representing the set of "positive" points.
//! The concept starts as "unknown" (all points possible) and we refine it:
//!
//! - Positive example x: the point x must be IN the concept
//! - Negative example x: the point x must NOT be in the concept
//!
//! We use two BDDs:
//! - `must_include`: points that MUST be in the concept (from positive examples)
//! - `may_include`: points that MAY be in the concept (not yet excluded)
//!
//! The concept is consistent iff must_include ⊆ may_include.
//!
//! Run with: cargo run --example concept_learning --release

use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var;

/// An example (assignment) with its classification.
#[derive(Debug, Clone)]
struct Example {
    /// Variable assignments: (var_index, value)
    assignment: Vec<(usize, bool)>,
    /// True = positive example, False = negative example
    is_positive: bool,
}

impl Example {
    fn positive(assignment: Vec<(usize, bool)>) -> Self {
        Example {
            assignment,
            is_positive: true,
        }
    }

    fn negative(assignment: Vec<(usize, bool)>) -> Self {
        Example {
            assignment,
            is_positive: false,
        }
    }
}

/// A concept learner using incremental BDD operations.
///
/// Maintains two BDDs:
/// - `must_include`: lower bound — points that MUST be in the concept
/// - `may_include`: upper bound — points that MAY be in the concept
///
/// Invariant: must_include ⊆ may_include (otherwise inconsistent)
struct ConceptLearner {
    bdd: Rc<Bdd>,
    /// Variables representing each input bit
    input_vars: Vec<Var>,
    /// Lower bound: points that must be included (from positive examples)
    must_include: Ref,
    /// Upper bound: points that may be included (negatives excluded)
    may_include: Ref,
    /// Number of examples seen
    example_count: usize,
}

impl ConceptLearner {
    /// Create a new concept learner for functions of n variables.
    fn new(bdd: Rc<Bdd>, num_vars: usize) -> Self {
        let input_vars: Vec<Var> = (1..=num_vars).map(|i| Var::new(i as u32)).collect();

        // Initially: must_include = ∅, may_include = all points
        let must_include = bdd.zero();
        let may_include = bdd.one();

        ConceptLearner {
            bdd,
            input_vars,
            must_include,
            may_include,
            example_count: 0,
        }
    }

    /// Encode an assignment as a BDD (conjunction of literals).
    fn encode_assignment(&self, assignment: &[(usize, bool)]) -> Ref {
        let mut result = self.bdd.one();
        for &(var_idx, value) in assignment {
            let var_ref = self.bdd.mk_var(self.input_vars[var_idx]);
            let lit = if value { var_ref } else { -var_ref };
            result = self.bdd.apply_and(result, lit);
        }
        result
    }

    /// Check consistency: must_include ⊆ may_include
    fn is_consistent(&self) -> bool {
        // must ⊆ may  iff  must ∧ ¬may = ∅
        let violation = self.bdd.apply_and(self.must_include, -self.may_include);
        self.bdd.is_zero(violation)
    }

    /// Add a training example and update the bounds.
    fn add_example(&mut self, example: Example) -> LearningResult {
        let point = self.encode_assignment(&example.assignment);
        self.example_count += 1;

        if example.is_positive {
            // Positive: point must be in the concept
            let old_must = self.must_include;
            self.must_include = self.bdd.apply_or(self.must_include, point);

            if !self.is_consistent() {
                return LearningResult::Inconsistent;
            }

            if self.must_include == old_must {
                LearningResult::AlreadyKnown
            } else {
                LearningResult::Refined {
                    must_include_size: self.count_satisfying(self.must_include),
                    may_include_size: self.count_satisfying(self.may_include),
                }
            }
        } else {
            // Negative: point must NOT be in the concept
            let old_may = self.may_include;
            self.may_include = self.bdd.apply_and(self.may_include, -point);

            if !self.is_consistent() {
                return LearningResult::Inconsistent;
            }

            if self.may_include == old_may {
                LearningResult::AlreadyKnown
            } else {
                LearningResult::Refined {
                    must_include_size: self.count_satisfying(self.must_include),
                    may_include_size: self.count_satisfying(self.may_include),
                }
            }
        }
    }

    /// Count satisfying assignments
    fn count_satisfying(&self, bdd_ref: Ref) -> u64 {
        use num_traits::ToPrimitive;
        self.bdd.sat_count(bdd_ref, self.input_vars.len()).to_u64().unwrap_or(0)
    }

    /// Check if learning has converged (must = may)
    fn is_converged(&self) -> bool {
        self.must_include == self.may_include
    }

    /// Get the "most specific" concept (must_include)
    fn get_lower_bound(&self) -> Ref {
        self.must_include
    }

    /// Get the "most general" concept (may_include)
    fn get_upper_bound(&self) -> Ref {
        self.may_include
    }

    /// Predict using the lower bound (conservative: only predict true if certain)
    fn predict_conservative(&self, assignment: &[(usize, bool)]) -> Option<bool> {
        if !self.is_consistent() {
            return None;
        }

        let point = self.encode_assignment(assignment);

        // Definitely in (in lower bound)
        let in_must = !self.bdd.is_zero(self.bdd.apply_and(point, self.must_include));
        // Definitely out (not in upper bound)
        let in_may = !self.bdd.is_zero(self.bdd.apply_and(point, self.may_include));

        if in_must {
            Some(true)
        } else if !in_may {
            Some(false)
        } else {
            None // Uncertain
        }
    }

    /// Get the uncertainty region (may - must)
    fn uncertainty_size(&self) -> u64 {
        let uncertain = self.bdd.apply_and(self.may_include, -self.must_include);
        self.count_satisfying(uncertain)
    }
}

/// Result of adding a training example.
#[derive(Debug)]
enum LearningResult {
    /// Example refined the bounds
    Refined { must_include_size: u64, may_include_size: u64 },
    /// Example was already consistent with bounds
    AlreadyKnown,
    /// Example contradicts previous examples
    Inconsistent,
}

fn main() {
    println!("=== Concept Learning via Incremental Synthesis ===\n");

    // We'll learn a simple concept over 4 boolean variables
    // The target concept is: (x0 ∧ x1) ∨ (x2 ∧ x3)

    let bdd = Rc::new(Bdd::default());
    let mut learner = ConceptLearner::new(bdd.clone(), 4);

    println!("Target concept: (x0 ∧ x1) ∨ (x2 ∧ x3)");
    println!("Learning from examples...\n");

    // Assert initial state: must=0, may=16 (all 2^4 points possible)
    let initial_must = learner.count_satisfying(learner.get_lower_bound());
    let initial_may = learner.count_satisfying(learner.get_upper_bound());
    let initial_uncertain = learner.uncertainty_size();

    assert_eq!(initial_must, 0, "Initially must-include should be empty");
    assert_eq!(initial_may, 16, "Initially may-include should have all 16 points");
    assert_eq!(initial_uncertain, 16, "Initially all 16 points should be uncertain");

    println!(
        "Initial: must={}, may={}, uncertain={}\n",
        initial_must, initial_may, initial_uncertain
    );

    // Training examples
    let examples = vec![
        // Positive examples (in the concept)
        Example::positive(vec![(0, true), (1, true), (2, false), (3, false)]), // 1100 → (x0∧x1)
        Example::positive(vec![(0, false), (1, false), (2, true), (3, true)]), // 0011 → (x2∧x3)
        Example::positive(vec![(0, true), (1, true), (2, true), (3, true)]),   // 1111 → both
        // Negative examples (not in the concept)
        Example::negative(vec![(0, true), (1, false), (2, false), (3, false)]), // 1000
        Example::negative(vec![(0, false), (1, true), (2, false), (3, false)]), // 0100
        Example::negative(vec![(0, false), (1, false), (2, true), (3, false)]), // 0010
        Example::negative(vec![(0, false), (1, false), (2, false), (3, true)]), // 0001
        Example::negative(vec![(0, false), (1, false), (2, false), (3, false)]), // 0000
    ];

    for (i, example) in examples.into_iter().enumerate() {
        let label = if example.is_positive { "+" } else { "-" };
        let bits: String = example.assignment.iter().map(|(_, v)| if *v { '1' } else { '0' }).collect();

        let result = learner.add_example(example);

        match &result {
            LearningResult::Refined {
                must_include_size,
                may_include_size,
            } => {
                let uncertain = may_include_size - must_include_size;
                println!(
                    "Example {}: {} {} → must={}, may={}, uncertain={}",
                    i + 1,
                    label,
                    bits,
                    must_include_size,
                    may_include_size,
                    uncertain
                );

                // Assert bounds are monotonic
                assert!(learner.is_consistent(), "Bounds must remain consistent");
            }
            LearningResult::AlreadyKnown => {
                println!("Example {}: {} {} → Already known (no change)", i + 1, label, bits);
            }
            LearningResult::Inconsistent => {
                println!("Example {}: {} {} → INCONSISTENT!", i + 1, label, bits);
                panic!("Example should not be inconsistent!");
            }
        }
    }

    // Assert final state after all examples
    let final_must = learner.count_satisfying(learner.get_lower_bound());
    let final_may = learner.count_satisfying(learner.get_upper_bound());
    let final_uncertain = learner.uncertainty_size();

    assert_eq!(final_must, 3, "After examples, must-include should have 3 points: 0011, 1100, 1111");
    assert_eq!(final_may, 11, "After examples, may-include should have 11 points");
    assert_eq!(final_uncertain, 8, "After examples, 8 points should still be uncertain");
    assert!(learner.is_consistent(), "Final state should be consistent");
    assert!(!learner.is_converged(), "Should not have fully converged (uncertain points remain)");

    println!("\n--- Learning Summary ---\n");
    println!("Converged: {}", learner.is_converged());
    println!("Consistent: {}", learner.is_consistent());
    println!("Uncertainty: {} points", learner.uncertainty_size());

    // Test predictions
    println!("\n--- Predictions on All Points ---\n");

    println!("bits | prediction | target | match");
    println!("-----|------------|--------|------");

    let mut correct = 0;
    let mut total = 0;

    for x0 in [false, true] {
        for x1 in [false, true] {
            for x2 in [false, true] {
                for x3 in [false, true] {
                    let assignment = vec![(0, x0), (1, x1), (2, x2), (3, x3)];
                    let bits: String = assignment.iter().map(|(_, v)| if *v { '1' } else { '0' }).collect();

                    let target = (x0 && x1) || (x2 && x3);
                    let prediction = learner.predict_conservative(&assignment);

                    let pred_str = match prediction {
                        Some(true) => "true ",
                        Some(false) => "false",
                        None => "  ?  ",
                    };

                    let target_str = if target { "true " } else { "false" };

                    let match_str = match prediction {
                        Some(p) if p == target => {
                            correct += 1;
                            total += 1;
                            "  ✓"
                        }
                        Some(_) => {
                            total += 1;
                            "  ✗"
                        }
                        None => "  -",
                    };

                    println!("{}  |   {}    |  {}  | {}", bits, pred_str, target_str, match_str);
                }
            }
        }
    }

    println!("\nAccuracy on certain predictions: {}/{}", correct, total);

    // Assert prediction accuracy
    assert_eq!(correct, 8, "Should have 8 correct confident predictions");
    assert_eq!(total, 8, "Should have made 8 confident predictions total");

    // Count uncertain predictions
    let mut uncertain_count = 0;
    for x0 in [false, true] {
        for x1 in [false, true] {
            for x2 in [false, true] {
                for x3 in [false, true] {
                    let assignment = vec![(0, x0), (1, x1), (2, x2), (3, x3)];
                    if learner.predict_conservative(&assignment).is_none() {
                        uncertain_count += 1;
                    }
                }
            }
        }
    }
    assert_eq!(uncertain_count, 8, "Should have 8 uncertain predictions");

    // Show which points are in the learned "must" set
    println!("\n--- Learned Must-Include Set ---\n");

    let mut must_set_bits = Vec::new();

    for x0 in [false, true] {
        for x1 in [false, true] {
            for x2 in [false, true] {
                for x3 in [false, true] {
                    let assignment = vec![(0, x0), (1, x1), (2, x2), (3, x3)];
                    let point = learner.encode_assignment(&assignment);
                    if !bdd.is_zero(bdd.apply_and(point, learner.get_lower_bound())) {
                        let bits: String = assignment.iter().map(|(_, v)| if *v { '1' } else { '0' }).collect();
                        let reason = match (x0 && x1, x2 && x3) {
                            (true, true) => "(x0∧x1) AND (x2∧x3)",
                            (true, false) => "(x0∧x1)",
                            (false, true) => "(x2∧x3)",
                            _ => "?",
                        };
                        println!("  {} ← {}", bits, reason);
                        must_set_bits.push(bits);
                    }
                }
            }
        }
    }

    // Assert must-include set contains exactly the three positive examples
    assert_eq!(must_set_bits.len(), 3, "Must-include set should contain exactly 3 points");
    assert!(must_set_bits.contains(&"0011".to_string()), "Must-include should contain 0011");
    assert!(must_set_bits.contains(&"1100".to_string()), "Must-include should contain 1100");
    assert!(must_set_bits.contains(&"1111".to_string()), "Must-include should contain 1111");

    // Demonstrate inconsistency detection
    println!("\n--- Demonstrating Inconsistency Detection ---\n");

    let mut learner2 = ConceptLearner::new(bdd.clone(), 2);
    println!("New learner with 2 variables");

    let result = learner2.add_example(Example::positive(vec![(0, false), (1, false)]));
    println!("Add +00: {:?}", result);
    assert!(learner2.is_consistent(), "Should be consistent after first example");
    assert_eq!(
        learner2.count_satisfying(learner2.get_lower_bound()),
        1,
        "Must-include should have 1 point"
    );

    let result = learner2.add_example(Example::negative(vec![(0, false), (1, false)]));
    println!("Add -00 (contradicts +00): {:?}", result);

    // Assert inconsistency was detected
    match result {
        LearningResult::Inconsistent => {
            println!("✓ Inconsistency correctly detected!");
            assert!(!learner2.is_consistent(), "Learner should be marked inconsistent");
        }
        _ => panic!("Should have detected inconsistency!"),
    }

    println!("\n=== All Assertions Passed! ===");
}
