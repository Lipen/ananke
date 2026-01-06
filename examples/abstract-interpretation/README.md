# Abstract Interpretation (BDD/SDD-guided)

This crate is an abstract interpretation case study: a small imperative AST, several abstract
domains, optional path-sensitive control tracking (BDD/SDD), and a fixpoint engine for loops.

If you want to start reading code, begin with:

- `src/lib.rs` (crate overview and module map)
- `src/domain.rs` (`AbstractDomain`: lattice + widening/narrowing)
- `src/fixpoint.rs` (`FixpointEngine`: least/greatest fixpoints)
- `src/expr.rs` (the AST used by transfer functions)

## Core idea

The design follows the standard abstract interpretation pattern:

```text
Abstract domain:  (D, ⊑, ⊥, ⊤, ⊔, ⊓, ∇, △)
Concretization:   γ : D -> P(States)
Transfer:         ⟦stmt⟧♯ : D -> D
Loop invariant:   lfp(F) computed by iteration with widening/narrowing
```

Read `a ⊑ b` as "`a` is at least as precise as `b`".

## What’s included

The crate intentionally contains a mix of "classic" and "toy-but-illustrative" domains:

- Numeric domains: interval, sign, constant, congruence
- Control domains: BDD and SDD control state (for path sensitivity)
- Composition: (reduced) products to combine independent components
- Structured / non-numeric examples: points-to, types, automata, string abstractions

## Quick start

From this directory:

```bash
cargo test
cargo test --doc
```

To browse rustdoc:

```bash
cargo doc --open
```

For performance experiments, prefer release mode (especially for BDD-heavy examples):

```bash
cargo run --release --example traffic_light
```

## Examples

The `examples/` directory contains runnable end-to-end analyses.
Here’s a representative selection:

- Basics: `sign_analysis`, `constant_propagation`, `combined_analysis`
- Fixpoints/loops: `simple_loops`, `loop_optimization`, `transfer_example`
- Path sensitivity: `traffic_light`, `mode_controller`, `protocol_fsm`, `sdd_control`, `sdd_path_interval`
- Pointers: `pointsto_example`
- Strings/regex/automata: `string_concatenation`, `string_constant_and_length`, `regex_analysis`, `automata_analysis`
- Types and security: `dynamic_type_check`, `security_and_normalization`, `input_validation`

Run any example via:

```bash
cargo run --example sign_analysis
```

## API sketch

The two core traits are [`AbstractDomain`] (lattice interface) and [`NumericDomain`] (adds
transformers for the numeric expression language).

And the fixpoint driver:

```rust
use abstract_interpretation::{AbstractDomain, FixpointEngine, IntervalDomain};

let domain = IntervalDomain;
let extrema = (domain.bottom(), domain.top());

let engine = FixpointEngine::new(domain);
```

For exact signatures and the intended laws, prefer the rustdoc on `AbstractDomain`, `NumericDomain`,
and `FixpointEngine`.

## Guide (Typst)

There is a companion guide under `guide/`.

```bash
cd guide
typst compile main.typ guide.pdf
```

## Project layout

```text
abstract-interpretation/
├── src/        # library code
├── examples/   # runnable case studies
├── tests/      # integration tests
└── guide/      # Typst guide (main.typ)
```

## Dependencies

This crate depends on the Ananke BDD/SDD crates:

```toml
[dependencies]
ananke-bdd = { path = "../../ananke-bdd" }
ananke-sdd = { path = "../../ananke-sdd" }
```

## References

Foundational abstract interpretation papers:

- Cousot & Cousot (1977): _"Abstract Interpretation: A Unified Lattice Model for Static Analysis of Programs by Construction or Approximation of Fixpoints"_
- Cousot & Cousot (1979): _"Systematic Design of Program Analysis Frameworks"_

Background reading that motivated some of the "case study" directions:

- Bryant (1986): _"Graph-Based Algorithms for Boolean Function Manipulation"_
- Granger (1989): _"Static Analysis of Arithmetical Congruences"_
- Miné (2006): _"The Octagon Abstract Domain"_
- Andersen (1994): _"Program Analysis and Specialization for the C Programming Language"_
- Steensgaard (1996): _"Points-to Analysis in Almost Linear Time"_
- Calcagno et al. (2015): _"Moving Fast with Software Verification"_

## Contributing

Contributions are welcome! This project is part of the larger `ananke` ecosystem.

- **Bug reports**: Open an issue with a minimal reproduction
- **New domains**: Add domain implementation with tests
- **Examples**: Demonstrate new analysis capabilities
- **Guide improvements**: Enhance explanations or add exercises

## License

MIT License --- see LICENSE file for details.

## Acknowledgments

This implementation builds on decades of research in abstract interpretation and symbolic verification.
Special thanks to Patrick and Radhia Cousot for pioneering abstract interpretation, and to Randal Bryant for introducing BDDs.

The `ananke` library and this framework are open-source projects welcoming community contributions.
