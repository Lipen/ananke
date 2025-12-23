# Incremental Decision Diagrams

A case study implementing incremental algorithms for BDD-based symbolic systems.

## The Core Idea

Traditional BDD algorithms recompute results from scratch whenever the system changes.
For evolving systems — where transitions are added, properties are refined, or constraints accumulate — this is wasteful.

**Incremental algorithms** reuse previous results where possible:

- Full recompute:

    $$ \text{System}_0 \xrightarrow{\text{change}} \text{System}_1 \xrightarrow{\text{[full compute]}} \text{Result}_1 $$

- Incremental:

    $$ \text{System}_0 \xrightarrow{\text{change}} \text{System}_1 \xrightarrow{\text{[update from Result}_0\text{]}} \text{Result}_1 $$

The key insight is that a *semantic delta* (what changed) is often much smaller than the full system.
By tracking deltas and propagating their effects, we can avoid redundant work.

---

## Delta Representation

A **Delta** represents a semantic change to a BDD-backed set:

```rust
pub struct Delta {
    pub added: Option<Ref>,    // Elements being added
    pub removed: Option<Ref>,  // Elements being removed
}
```

**Invariant**: $\texttt{added} \cap \texttt{removed} = \varnothing$ — an element cannot be both added and removed.

**Application**: Given a set $S$ and delta $\Delta = (A^{+}, A^{-})$:

$$
    S' = (S \cup A^{+}) \setminus A^{-}
$$

In BDD operations:

```rust
fn apply(&self, bdd: &Bdd, set: Ref) -> Ref {
    let with_added = bdd.apply_or(set, self.added);
    bdd.apply_and(with_added, -self.removed)  // complement for set difference
}
```

---

## Effect Classification

Every delta application is classified by its *effect*:

| Effect | Meaning | Action |
| ------ | ------- | ------ |
| `NoChange` | Delta had no semantic effect | Skip recomputation |
| `LocalChange` | Only part of the structure affected | Incremental update |
| `GlobalRebuildRequired` | Change too disruptive | Fall back to full recompute |

This classification enables **adaptive algorithms** that choose the cheapest update strategy.

---

## Incremental Reachability

The core pattern for incremental forward reachability:

### On Transition Addition

When transitions are *added*, new states may become reachable:

1. Find affected states: sources of new edges that are currently reachable
    - $ \texttt{affected} = \exists s'. \Delta T(s, s') \land \text{Reach}(s) $

2. Compute new frontier: where can we reach from affected states?
    - $ \texttt{frontier} = \text{Image}(\texttt{affected}) \setminus \text{Reach} $

3. Propagate forward: extend reachability from frontier while $\texttt{frontier} \neq \varnothing$:
    - $ \texttt{frontier} = \text{Image}(\texttt{frontier}) \setminus \text{Reach} $
    - $ \text{Reach} = \text{Reach} \cup \texttt{frontier} $

**Key optimization**: If no reachable state has new outgoing edges, reachability is unchanged.

### On Transition Removal

When transitions are *removed*, some states may become unreachable:

1. Find at-risk states: targets of removed edges (non-initial, currently reachable)
    - $\texttt{at\_risk} = \exists s. \Delta T(s, s') \land \text{Reach}(s') \land \lnot \text{Init}(s')$

2. If $\texttt{at\_risk} \neq \varnothing$: conservative approach $\Rightarrow$ full rebuild
   - (Incremental shrinking is possible but complex)

---

## Incremental Safety Verification

Safety property: $\text{Reach} \subseteq \text{Invariant}$ (all reachable states satisfy the invariant).

### Update Patterns

| System Change | Previous Status | Incremental Action |
| ------------- | --------------- | ------------------ |
| Transitions added | Safe | Check if new reachable states violate invariant |
| Transitions added | Unsafe | Still unsafe (can't become safe by adding) |
| Transitions removed | Safe | Still safe (removal can't introduce violations) |
| Transitions removed | Unsafe | Check if violation still reachable |
| Invariant strengthened | Safe | Recheck (may become unsafe) |
| Invariant weakened | Unsafe | Check if old violations still exist |

---

## Incremental Constraint Synthesis

For constraint satisfaction, maintain a *solution space* BDD:

```rust
pub struct IncrementalConstraintSynthesizer {
    solution_space: Ref,    // Current valid configurations
    constraints: Vec<Ref>,  // For potential removal
}
```

### Constraint Addition (Monotonic Shrinking)

Adding constraint $C$:

```rust
fn add_constraint(&mut self, c: Ref) -> ConstraintEffect {
    let new_space = bdd.apply_and(self.solution_space, c);

    if bdd.is_zero(new_space) {
        return ConstraintEffect::Unsat;  // Conflict!
    }
    if new_space == self.solution_space {
        return ConstraintEffect::NoEffect;  // Already implied
    }

    self.solution_space = new_space;
    ConstraintEffect::Shrunk { removed_nodes: ... }
}
```

**Key insight**: Constraint addition is *monotonic* — the space only shrinks.
This makes incremental updates simple: just conjoin the new constraint.

---

## Project Structure

```
src/
├── delta.rs           # Delta type and operations
├── traits.rs          # IncrementalFixpoint, IncrementalVerifier, etc.
├── incremental_ts.rs  # IncrementalTransSystem, IncrementalReachabilityFixpoint
├── safety.rs          # IncrementalSafetyChecker
├── synthesis.rs       # IncrementalConstraintSynthesizer
└── metrics.rs         # Performance tracking
```

### Reading Order for Study

1. **Start with `delta.rs`**: Understand the `Delta` type and `DeltaEffect` enum.
   These are the building blocks for all incremental operations.

2. **Read `traits.rs`**: See the trait hierarchy defining incremental interfaces.
   Focus on `IncrementalFixpoint` and `IncrementalSynthesizer`.

3. **Study `incremental_ts.rs`**: The core incremental reachability algorithm.
   Key methods: `add_transitions()`, `remove_transitions()`, `extend_reachability()`.

4. **Examine `synthesis.rs`**: The simplest complete example.
   `add_constraint()` shows the monotonic update pattern.

5. **Review `safety.rs`**: Combines reachability with property checking.
   See `update_transitions()` for the incremental verification logic.

### Key Patterns to Notice

- **Effect classification**: Every update returns `NoChange`, `LocalChange`, or `GlobalRebuildRequired`
- **Caching with invalidation**: `reach: Option<Ref>` pattern with version tracking
- **Monotonicity exploitation**: Addition-only deltas enable simpler incremental updates
- **Conservative fallback**: When incremental is too complex, fall back to full rebuild

---

## Running the Examples

### Feature Configuration

Demonstrates incremental constraint satisfaction for product configuration:

```bash
cargo run --example feature_config --release
```

Shows how solution space shrinks as constraints accumulate, with effect classification at each step.

### Simple Reachability

Basic incremental reachability on a small state machine:

```bash
cargo run --example simple_reachability --release
```

---

## When Incremental Helps (and When It Doesn't)

**Incremental wins when**:

- Deltas are small relative to the system
- Changes are monotonic (additions only, or removals only)
- Previous computation was expensive

**Incremental loses when**:

- Delta affects most of the structure
- Mixed additions/removals require complex reasoning
- Overhead of tracking exceeds savings

The `DeltaEffect` classification helps detect when to fall back to full rebuild.
