//! Feature Model Configuration Case Study
//!
//! This example demonstrates incremental constraint-based synthesis
//! for product line configuration. We model a software product line
//! with features and incrementally add user preferences and constraints.
//!
//! Run with: cargo run --example feature_config --release

use std::rc::Rc;
use std::time::Instant;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use ananke_bdd::types::Var;
use incremental_dd::synthesis::SynthesizerBuilder;
use incremental_dd::traits::{ConstraintEffect, IncrementalSynthesizer};

/// A simple feature model for a car configuration system
struct CarFeatureModel {
    bdd: Rc<Bdd>,
    // Features
    electric: Var,      // Electric powertrain
    hybrid: Var,        // Hybrid powertrain
    gasoline: Var,      // Gasoline powertrain
    premium_audio: Var, // Premium audio system
    basic_audio: Var,   // Basic audio system
    sunroof: Var,       // Sunroof
    heated_seats: Var,  // Heated seats
    sport_package: Var, // Sport package
    eco_package: Var,   // Eco package
}

impl CarFeatureModel {
    fn new(bdd: Rc<Bdd>) -> Self {
        CarFeatureModel {
            bdd,
            electric: Var::new(1),
            hybrid: Var::new(2),
            gasoline: Var::new(3),
            premium_audio: Var::new(4),
            basic_audio: Var::new(5),
            sunroof: Var::new(6),
            heated_seats: Var::new(7),
            sport_package: Var::new(8),
            eco_package: Var::new(9),
        }
    }

    /// Get all feature variables
    fn all_features(&self) -> Vec<Var> {
        vec![
            self.electric,
            self.hybrid,
            self.gasoline,
            self.premium_audio,
            self.basic_audio,
            self.sunroof,
            self.heated_seats,
            self.sport_package,
            self.eco_package,
        ]
    }

    /// Constraint: exactly one powertrain
    fn powertrain_constraint(&self) -> Ref {
        let e = self.bdd.mk_var(self.electric);
        let h = self.bdd.mk_var(self.hybrid);
        let g = self.bdd.mk_var(self.gasoline);

        // Exactly one of e, h, g
        // (e ∧ ¬h ∧ ¬g) ∨ (¬e ∧ h ∧ ¬g) ∨ (¬e ∧ ¬h ∧ g)
        let only_e = self.bdd.apply_and(self.bdd.apply_and(e, -h), -g);
        let only_h = self.bdd.apply_and(self.bdd.apply_and(-e, h), -g);
        let only_g = self.bdd.apply_and(self.bdd.apply_and(-e, -h), g);

        self.bdd.apply_or(self.bdd.apply_or(only_e, only_h), only_g)
    }

    /// Constraint: exactly one audio system
    fn audio_constraint(&self) -> Ref {
        let p = self.bdd.mk_var(self.premium_audio);
        let b = self.bdd.mk_var(self.basic_audio);

        // Exactly one of premium or basic
        self.bdd.apply_xor(p, b)
    }

    /// Constraint: sport package requires gasoline or hybrid
    fn sport_requires_power(&self) -> Ref {
        let sport = self.bdd.mk_var(self.sport_package);
        let g = self.bdd.mk_var(self.gasoline);
        let h = self.bdd.mk_var(self.hybrid);

        // sport → (gasoline ∨ hybrid)
        // ≡ ¬sport ∨ gasoline ∨ hybrid
        self.bdd.apply_or(self.bdd.apply_or(-sport, g), h)
    }

    /// Constraint: eco package requires electric or hybrid
    fn eco_requires_efficient(&self) -> Ref {
        let eco = self.bdd.mk_var(self.eco_package);
        let e = self.bdd.mk_var(self.electric);
        let h = self.bdd.mk_var(self.hybrid);

        // eco → (electric ∨ hybrid)
        self.bdd.apply_or(self.bdd.apply_or(-eco, e), h)
    }

    /// Constraint: sport and eco are mutually exclusive
    fn sport_eco_exclusive(&self) -> Ref {
        let sport = self.bdd.mk_var(self.sport_package);
        let eco = self.bdd.mk_var(self.eco_package);

        // ¬(sport ∧ eco)
        -self.bdd.apply_and(sport, eco)
    }

    /// Constraint: premium audio requires sunroof or heated seats
    fn premium_requires_luxury(&self) -> Ref {
        let premium = self.bdd.mk_var(self.premium_audio);
        let sunroof = self.bdd.mk_var(self.sunroof);
        let heated = self.bdd.mk_var(self.heated_seats);

        // premium → (sunroof ∨ heated_seats)
        self.bdd.apply_or(self.bdd.apply_or(-premium, sunroof), heated)
    }
}

fn main() {
    env_logger::init();

    println!("=== Feature Model Configuration Demo ===\n");

    let bdd = Rc::new(Bdd::default());
    let fm = CarFeatureModel::new(bdd.clone());

    // Create synthesizer with all features
    let mut synth = SynthesizerBuilder::new(bdd.clone()).add_variables(fm.all_features()).build();

    let initial_count = synth.solution_count().unwrap_or(0);
    println!("Initial solution space: {} configurations\n", initial_count);
    assert_eq!(initial_count, 512, "Initial: 2^9 = 512 configurations");

    // === Phase 1: Add domain constraints ===
    println!("Phase 1: Domain Constraints\n");

    let constraints = vec![
        ("Exactly one powertrain", fm.powertrain_constraint()),
        ("Exactly one audio", fm.audio_constraint()),
        ("Sport requires gas/hybrid", fm.sport_requires_power()),
        ("Eco requires electric/hybrid", fm.eco_requires_efficient()),
        ("Sport/eco exclusive", fm.sport_eco_exclusive()),
        ("Premium requires luxury", fm.premium_requires_luxury()),
    ];

    let start = Instant::now();
    for (name, constraint) in &constraints {
        let effect = synth.add_constraint(*constraint);
        let count = synth.solution_count().unwrap_or(0);
        println!("  + {}: {:?}, {} configs remain", name, effect, count);
    }
    let domain_time = start.elapsed();
    println!("  Domain constraints time: {:?}\n", domain_time);

    let after_domain = synth.solution_count().unwrap_or(0);
    println!("After domain constraints: {} valid configurations\n", after_domain);
    assert!(after_domain > 0, "Domain constraints must leave at least one valid config");
    assert!(after_domain < initial_count, "Domain constraints must reduce solution space");
    println!(
        "  ✓ Constraints reduced space to {:.1}% of initial\n",
        (after_domain as f64 / initial_count as f64) * 100.0
    );

    // === Phase 2: User preferences ===
    println!("Phase 2: User Preferences\n");

    // User wants electric or hybrid (eco-conscious)
    let eco_preference = bdd.apply_or(bdd.mk_var(fm.electric), bdd.mk_var(fm.hybrid));

    let start = Instant::now();
    let effect = synth.add_constraint(eco_preference);
    let pref_time = start.elapsed();

    println!("  + Want electric or hybrid: {:?}", effect);
    println!("  Remaining: {} configurations", synth.solution_count().unwrap_or(0));
    println!("  Time: {:?}\n", pref_time);

    // User wants heated seats
    let heated = bdd.mk_var(fm.heated_seats);
    let start = Instant::now();
    let effect = synth.add_constraint(heated);
    let time2 = start.elapsed();

    println!("  + Want heated seats: {:?}", effect);
    println!("  Remaining: {} configurations", synth.solution_count().unwrap_or(0));
    println!("  Time: {:?}\n", time2);

    // User wants premium audio
    let premium = bdd.mk_var(fm.premium_audio);
    let start = Instant::now();
    let effect = synth.add_constraint(premium);
    let time3 = start.elapsed();

    println!("  + Want premium audio: {:?}", effect);
    println!("  Remaining: {} configurations", synth.solution_count().unwrap_or(0));
    println!("  Time: {:?}\n", time3);

    // === Phase 3: Additional constraints ===
    println!("Phase 3: Budget/Availability Constraints\n");

    // Sunroof not available
    let no_sunroof = -bdd.mk_var(fm.sunroof);
    let start = Instant::now();
    let effect = synth.add_constraint(no_sunroof);
    let time4 = start.elapsed();

    println!("  + Sunroof unavailable: {:?}", effect);
    println!("  Remaining: {} configurations", synth.solution_count().unwrap_or(0));
    println!("  Time: {:?}\n", time4);

    // User also wants sport package
    let sport = bdd.mk_var(fm.sport_package);

    // Check if this would cause UNSAT before adding
    if synth.would_cause_unsat(sport) {
        println!("  ! Sport package would cause UNSAT");
        println!("    (Sport requires gas/hybrid, but user chose electric/hybrid)");
        println!("    (With hybrid, sport is possible, so let's see...)\n");
    }

    let start = Instant::now();
    let effect = synth.add_constraint(sport);
    let time5 = start.elapsed();

    println!("  + Want sport package: {:?}", effect);
    println!("  Remaining: {} configurations", synth.solution_count().unwrap_or(0));
    println!("  Time: {:?}\n", time5);

    // === Phase 4: Try conflicting constraint ===
    println!("Phase 4: Conflicting Constraint\n");

    // User now wants eco package (conflicts with sport)
    let eco = bdd.mk_var(fm.eco_package);

    if synth.would_cause_unsat(eco) {
        println!("  ! Eco package would cause UNSAT (conflicts with sport)");
    }

    let start = Instant::now();
    let effect = synth.add_constraint(eco);
    let time6 = start.elapsed();

    println!("  + Want eco package: {:?}", effect);
    println!("  Time: {:?}", time6);

    match effect {
        ConstraintEffect::Unsat => {
            println!("  CONFLICT DETECTED: Cannot have both sport and eco packages\n");
        }
        _ => {
            println!("  Remaining: {} configurations\n", synth.solution_count().unwrap_or(0));
        }
    }

    // === Summary ===
    println!("=== Summary ===");
    println!("Initial configurations: 512 (2^9)");
    println!("After domain constraints: {}", after_domain);
    println!("Constraint additions: {}", synth.constraint_count());
    assert!(synth.constraint_count() >= 6, "Should have at least 6 domain constraints");

    let metrics = synth.metrics();
    println!("\nIncremental Metrics:");
    println!("  No-effect constraints: {}", metrics.no_change_count);
    println!("  Shrinking constraints: {}", metrics.local_change_count);
    println!("  UNSAT detections: {}", metrics.global_rebuild_count);
    assert_eq!(
        metrics.global_rebuild_count, 1,
        "Should detect 1 UNSAT condition (eco+sport conflict)"
    );

    // Show a valid configuration from last SAT state (before eco constraint)
    // We need to revert to before the eco constraint for a valid config
    println!("\nNote: System is UNSAT after adding eco package (conflicts with sport)");
    println!("✓ All feature configuration tests passed!");
}
