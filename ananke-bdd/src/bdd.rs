//! Binary Decision Diagram (BDD) manager.
//!
//! This module provides a **reduced ordered BDD** (ROBDD) implementation with
//! **complement edges** and a **shared multi-rooted graph** representation.
//!
//! # Overview
//!
//! A BDD is a compact data structure for representing Boolean functions as directed
//! acyclic graphs. This implementation uses a manager-centric design where:
//!
//! - [`Bdd`] is the central manager that owns all nodes and handles operations
//! - [`Ref`] is a lightweight 32-bit handle to a node (index + complement flag)
//! - Nodes are stored in a shared pool with per-level hash tables for uniqueness
//!
//! See the [`Bdd`] struct documentation for a complete method reference.
//!
//! # Quick Start
//!
//! ```
//! use ananke_bdd::bdd::Bdd;
//!
//! let bdd = Bdd::default();
//!
//! // Create variables
//! let x = bdd.mk_var(1);
//! let y = bdd.mk_var(2);
//!
//! // Boolean operations
//! let f = bdd.apply_and(x, y);    // x ∧ y
//! let g = bdd.apply_or(x, -y);    // x ∨ ¬y
//! let h = bdd.apply_xor(x, y);    // x ⊕ y
//!
//! // Check properties
//! assert!(!bdd.is_zero(f));                     // satisfiable
//! assert!(bdd.is_zero(bdd.apply_and(x, -x)));   // contradiction
//! assert!(bdd.is_one(bdd.apply_or(x, -x)));     // tautology
//! ```

use std::cell;
use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

use log::debug;

use crate::bitset::BitSet;
use crate::cache::Cache;
use crate::node::Node;
use crate::reference::Ref;
use crate::reorder::ReorderStats;
use crate::subtable::Subtable;
use crate::types::{Level, Lit, NodeId, Var};
use crate::utils::OpKey;

/// The BDD manager: a shared multi-rooted graph with complement edges.
///
/// This is the central structure for creating and manipulating BDDs.
/// It maintains:
/// - A **node storage array** (`Vec<Node>`) for storing node data
/// - **Per-level subtables** for efficient hash-based node lookup
/// - An **operation cache** for memoizing ITE results
/// - An **explicit variable ordering** that can be dynamically changed
///
/// # Design
///
/// All BDD operations go through the manager.
/// The manager owns the storage and ensures:
/// - **Uniqueness**: Identical nodes are shared (hash consing via per-level subtables)
/// - **Reduction**: Redundant nodes are eliminated automatically
/// - **Canonicity**: Each function has exactly one representation
///
/// # Key Features
///
/// - **Complement edges**: Negation is O(1), just flip a bit — no new nodes created
/// - **Per-level subtables**: Efficient node lookup using intrusive hash tables
/// - **Dynamic reordering**: Variables can be reordered to minimize BDD size
/// - **Operation caching**: ITE results are memoized for performance
///
/// # Architecture
///
/// ```text
///                                 Bdd Manager
///  ┌─────────────────────────────────────────────────────────────────┐
///  │                                                                 │
///  │  nodes: Vec<Node>         cache: Cache      size_cache: Cache   │
///  │  ┌────────────────┐       ┌────────────┐    ┌────────────┐      │
///  │  │ [0] terminal   │◄──┐   │  ITE ops   │    │  size(f)   │      │
///  │  │ [1] node       │   │   │  memoized  │    │  memoized  │      │
///  │  │ [2] node       │   │   └────────────┘    └────────────┘      │
///  │  │ ...            │   │                                         │
///  │  └────────────────┘   │                                         │
///  │                       │                                         │
///  │  var_order: Vec<Var>  │   level_map: HashMap<Var, Level>        │
///  │   (level → variable)  │    (variable → level)                   │
///  │  ┌────────────────┐   │   ┌─────────────────────────────┐       │
///  │  │ [0] Var(1)     │   │   │  Var(1) → Level(0)          │       │
///  │  │ [1] Var(2)     │   │   │  Var(2) → Level(1)          │       │
///  │  │ [2] Var(3)     │   │   │  Var(3) → Level(2)          │       │
///  │  │ ...            │   │   │  ...                        │       │
///  │  └────────────────┘   │   └─────────────────────────────┘       │
///  │                       │                                         │
///  │  subtables: Vec<Subtable>                                       │
///  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐                │
///  │  │  Level 0    │ │  Level 1    │ │  Level 2    │ ...            │
///  │  │  (low,high) │ │  (low,high) │ │  (low,high) │                │
///  │  │  → NodeId   │ │  → NodeId   │ │  → NodeId   │                │
///  │  └─────────────┘ └─────────────┘ └─────────────┘                │
///  │                       │                                         │
///  └───────────────────────│─────────────────────────────────────────┘
///                          │
///                          ▼
///          Ref: 32-bit handle (31-bit NodeId + 1-bit complement)
///          ┌─────────────────────────────────┬───┐
///          │       Node Index (31 bits)      │ C │
///          └─────────────────────────────────┴───┘
///                                              └── Complement bit
///                                                   (negation)
/// ```
///
/// # Node Structure
///
/// Each node contains:
/// - `variable`: The decision variable at this node
/// - `low`: Child when variable is false (may be complemented)
/// - `high`: Child when variable is true (never complemented)
/// - `next`: Collision chain pointer for the hash table
///
/// # Invariants
///
/// - **Canonical form**: High edges are never complemented
/// - **Reduced**: No node has `low == high` (would be redundant)
/// - **Ordered**: Parent variable always precedes children in the ordering
/// - **Unique**: No two nodes have the same (variable, low, high) triple
///
/// # Thread Safety
///
/// The manager uses `RefCell` internally and is **not thread-safe**.
/// For concurrent use, wrap in appropriate synchronization primitives.
///
/// # Method Reference
///
/// ## Terminal Constants
///
/// - [`one()`][Bdd::one] — Returns the constant TRUE BDD
/// - [`zero()`][Bdd::zero] — Returns the constant FALSE BDD
/// - [`is_one()`][Bdd::is_one] — Checks if a BDD is the TRUE constant
/// - [`is_zero()`][Bdd::is_zero] — Checks if a BDD is the FALSE constant
/// - [`is_terminal()`][Bdd::is_terminal] — Checks if a BDD is a terminal (TRUE or FALSE)
///
/// ## BDD Construction
///
/// - [`mk_var()`][Bdd::mk_var] — Creates a BDD for a single variable
/// - [`mk_node()`][Bdd::mk_node] — Creates a BDD node with given children
/// - [`mk_cube()`][Bdd::mk_cube] — Creates a conjunction (AND) of literals
/// - [`mk_clause()`][Bdd::mk_clause] — Creates a disjunction (OR) of literals
/// - [`mk_true()`][Bdd::mk_true] — Alias for `one()`
/// - [`mk_false()`][Bdd::mk_false] — Alias for `zero()`
///
/// ## Boolean Operations
///
/// - [`apply_not()`][Bdd::apply_not] — Negation: `¬f` (O(1) with complement edges)
/// - [`apply_and()`][Bdd::apply_and] — Conjunction: `f ∧ g`
/// - [`apply_or()`][Bdd::apply_or] — Disjunction: `f ∨ g`
/// - [`apply_xor()`][Bdd::apply_xor] — Exclusive OR: `f ⊕ g`
/// - [`apply_eq()`][Bdd::apply_eq] — Equivalence: `f ↔ g`
/// - [`apply_imply()`][Bdd::apply_imply] — Implication: `f → g`
/// - [`apply_ite()`][Bdd::apply_ite] — If-then-else: `(f ∧ g) ∨ (¬f ∧ h)`
///
/// ## Quantification
///
/// - [`exists()`][Bdd::exists] — Existential quantification: `∃vars. f`
/// - [`forall()`][Bdd::forall] — Universal quantification: `∀vars. f`
/// - [`rel_product()`][Bdd::rel_product] — Relational product: `∃vars. (f ∧ g)`
///
/// ## Substitution & Cofactors
///
/// - [`cofactor_cube()`][Bdd::cofactor_cube] — Restrict `f` by setting variables
/// - [`compose()`][Bdd::compose] — Substitute variable `v` with BDD `g`
/// - [`substitute()`][Bdd::substitute] — Substitute variable with constant
/// - [`constrain()`][Bdd::constrain] — Generalized cofactor (Coudert & Madre)
///
/// ## Analysis
///
/// - [`size()`][Bdd::size] — Count of nodes in BDD
/// - [`descendants()`][Bdd::descendants] — All node IDs reachable from roots
/// - [`is_implies()`][Bdd::is_implies] — Check if `f → g` is a tautology
///
/// # Examples
///
/// ## Basic Usage
///
/// ```
/// use ananke_bdd::bdd::Bdd;
///
/// let bdd = Bdd::default();
///
/// // Create variables (1-indexed)
/// let x = bdd.mk_var(1);
/// let y = bdd.mk_var(2);
///
/// // Boolean operations
/// let f = bdd.apply_and(x, y);    // x ∧ y
/// let g = bdd.apply_or(x, -y);    // x ∨ ¬y  (note: -y is negation)
/// let h = bdd.apply_xor(x, y);    // x ⊕ y
///
/// // Check satisfiability and validity
/// assert!(!bdd.is_zero(f));                    // f is satisfiable
/// assert!(bdd.is_zero(bdd.apply_and(x, -x)));  // x ∧ ¬x is unsatisfiable
/// assert!(bdd.is_one(bdd.apply_or(x, -x)));    // x ∨ ¬x is a tautology
/// ```
///
/// ## Cubes and Clauses
///
/// ```
/// use ananke_bdd::bdd::Bdd;
///
/// let bdd = Bdd::default();
///
/// // Cube (conjunction): x₁ ∧ ¬x₂ ∧ x₃ using DIMACS-style literals
/// let cube = bdd.mk_cube([1, -2, 3]);
///
/// // Clause (disjunction): x₁ ∨ ¬x₂ ∨ x₃
/// let clause = bdd.mk_clause([1, -2, 3]);
///
/// // Evaluate by restricting variables
/// let result = bdd.cofactor_cube(clause, [1]);  // Set x₁=true
/// assert!(bdd.is_one(result));  // Clause becomes true
/// ```
///
/// ## Quantification
///
/// ```
/// use ananke_bdd::bdd::Bdd;
/// use ananke_bdd::types::Var;
///
/// let bdd = Bdd::default();
/// let x = bdd.mk_var(1);
/// let y = bdd.mk_var(2);
/// let f = bdd.apply_and(x, y);  // x ∧ y
///
/// // Existential: ∃x.(x ∧ y) = y
/// let ex = bdd.exists(f, [Var::new(1)]);
/// assert_eq!(ex, y);
///
/// // Universal: ∀x.(x ∧ y) = false (not true for all x)
/// let fa = bdd.forall(f, [Var::new(1)]);
/// assert!(bdd.is_zero(fa));
/// ```
///
/// ## Composition
///
/// ```
/// use ananke_bdd::bdd::Bdd;
/// use ananke_bdd::types::Var;
///
/// let bdd = Bdd::default();
/// let x = bdd.mk_var(1);
/// let y = bdd.mk_var(2);
/// let z = bdd.mk_var(3);
///
/// // f = x ∧ y
/// let f = bdd.apply_and(x, y);
///
/// // Substitute x with z: f[x ← z] = z ∧ y
/// let g = bdd.compose(f, Var::new(1), z);
/// assert_eq!(g, bdd.apply_and(z, y));
/// ```
pub struct Bdd {
    /// Node storage: Vec of Node, indexed by NodeId.
    /// Index 0 is the terminal node (Var::ZERO). Decision nodes start at index 1.
    nodes: RefCell<Vec<Node>>,
    /// Set of free (recycled) node indices available for reuse.
    free_set: RefCell<HashSet<NodeId>>,
    cache: RefCell<Cache<OpKey, Ref>>,
    size_cache: RefCell<Cache<Ref, u64>>,
    var_order: RefCell<Vec<Var>>,            // level -> variable
    level_map: RefCell<HashMap<Var, Level>>, // variable -> level
    subtables: RefCell<Vec<Subtable>>,       // level -> subtable
    next_var_id: Cell<u32>,                  // next variable ID to allocate
    config: BddConfig,                       // configuration
}

/// Configuration for the BDD manager.
///
/// Use this to customize initial capacities for advanced use cases.
/// For most uses, `Bdd::default()` is sufficient as all structures auto-resize.
///
/// # Example
///
/// ```
/// use ananke_bdd::bdd::{Bdd, BddConfig};
///
/// // Custom configuration for large problems
/// let config = BddConfig::default()
///     .with_initial_nodes(1 << 20)  // 1M nodes
///     .with_cache_bits(18);         // 256K cache entries
///
/// let bdd = Bdd::with_config(config);
/// ```
#[derive(Debug, Clone)]
pub struct BddConfig {
    /// Initial capacity for node storage.
    pub initial_nodes: usize,
    /// Cache size in bits (size = 2^bits).
    pub cache_bits: usize,
    /// Subtable bucket bits (buckets = 2^bits per level).
    pub subtable_bits: usize,
}

impl Default for BddConfig {
    fn default() -> Self {
        Self {
            initial_nodes: 1024, // Start small, will grow as needed
            cache_bits: 14,      // 16K cache entries
            subtable_bits: 12,   // 4K buckets per level
        }
    }
}

impl BddConfig {
    /// Set the initial node storage capacity.
    pub fn with_initial_nodes(mut self, capacity: usize) -> Self {
        self.initial_nodes = capacity;
        self
    }

    /// Set the cache size in bits (size = 2^bits).
    pub fn with_cache_bits(mut self, bits: usize) -> Self {
        self.cache_bits = bits;
        self
    }

    /// Set the subtable bucket bits (buckets = 2^bits per level).
    pub fn with_subtable_bits(mut self, bits: usize) -> Self {
        self.subtable_bits = bits;
        self
    }
}

impl Bdd {
    /// Creates a new BDD manager with the specified storage capacity.
    ///
    /// **Deprecated**: Prefer `Bdd::default()` or `Bdd::with_config()` instead.
    /// The BDD automatically resizes as needed, so pre-allocating capacity
    /// is usually unnecessary.
    ///
    /// # Arguments
    ///
    /// * `storage_bits` - Storage capacity in bits (must be ≤ 31). Typical values:
    ///   - 16: 65K nodes (small problems)
    ///   - 20: 1M nodes (default, medium problems)
    ///   - 24: 16M nodes (large problems)
    ///
    /// # Panics
    ///
    /// Panics if `storage_bits > 31`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// // Small BDD for simple problems
    /// let small_bdd = Bdd::new(16);
    /// assert_eq!(small_bdd.num_nodes(), 1);  // Just the terminal node
    ///
    /// // Large BDD for complex problems
    /// let large_bdd = Bdd::new(24);
    /// assert_eq!(large_bdd.num_nodes(), 1);
    /// ```
    #[deprecated = "Use Bdd::default() or Bdd::with_config() instead"]
    pub fn new(storage_bits: usize) -> Self {
        assert!(storage_bits <= 31, "Storage bits should be in the range 0..=31");
        let config = BddConfig::default().with_initial_nodes(1 << storage_bits);
        Self::with_config(config)
    }

    /// Creates a new BDD manager with the given configuration.
    ///
    /// For most use cases, `Bdd::default()` is sufficient. Use this method
    /// when you need to tune initial capacities for performance.
    ///
    /// # Example
    ///
    /// ```
    /// use ananke_bdd::bdd::{Bdd, BddConfig};
    ///
    /// let config = BddConfig::default()
    ///     .with_initial_nodes(1 << 18)
    ///     .with_cache_bits(16);
    ///
    /// let bdd = Bdd::with_config(config);
    /// ```
    pub fn with_config(config: BddConfig) -> Self {
        // Initialize node storage with the terminal node at index 0.
        // Terminal has variable 0 and invalid children (terminals have no children).
        let mut nodes = Vec::with_capacity(config.initial_nodes);
        nodes.push(Node::new(Var::ZERO, Ref::INVALID, Ref::INVALID));

        Self {
            nodes: RefCell::new(nodes),
            free_set: RefCell::new(HashSet::new()),
            cache: RefCell::new(Cache::new(config.cache_bits)),
            size_cache: RefCell::new(Cache::new(config.cache_bits)),
            var_order: RefCell::new(Vec::new()),
            level_map: RefCell::new(HashMap::new()),
            subtables: RefCell::new(Vec::new()),
            next_var_id: Cell::new(1), // Variables start at 1
            config,
        }
    }
}

// ============================================================================
// Trait implementations
// ============================================================================

impl Default for Bdd {
    fn default() -> Self {
        Bdd::with_config(BddConfig::default())
    }
}

impl Debug for Bdd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Bdd")
            .field("capacity", &self.nodes().capacity())
            .field("size", &self.num_nodes())
            // .field(
            //     "order",
            //     &format_args!(
            //         "[{}]",
            //         self.var_order().iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")
            //     ),
            // )
            .finish()
    }
}

// ============================================================================
// Internal state accessors
// ============================================================================

impl Bdd {
    pub fn nodes(&self) -> cell::Ref<'_, Vec<Node>> {
        self.nodes.borrow()
    }
    pub(crate) fn nodes_mut(&self) -> cell::RefMut<'_, Vec<Node>> {
        self.nodes.borrow_mut()
    }

    pub fn free_set(&self) -> cell::Ref<'_, HashSet<NodeId>> {
        self.free_set.borrow()
    }
    pub(crate) fn free_set_mut(&self) -> cell::RefMut<'_, HashSet<NodeId>> {
        self.free_set.borrow_mut()
    }

    pub fn var_order(&self) -> cell::Ref<'_, Vec<Var>> {
        self.var_order.borrow()
    }
    pub(crate) fn var_order_mut(&self) -> cell::RefMut<'_, Vec<Var>> {
        self.var_order.borrow_mut()
    }

    pub fn level_map(&self) -> cell::Ref<'_, HashMap<Var, Level>> {
        self.level_map.borrow()
    }
    pub(crate) fn level_map_mut(&self) -> cell::RefMut<'_, HashMap<Var, Level>> {
        self.level_map.borrow_mut()
    }

    pub fn subtables(&self) -> cell::Ref<'_, Vec<Subtable>> {
        self.subtables.borrow()
    }
    pub(crate) fn subtables_mut(&self) -> cell::RefMut<'_, Vec<Subtable>> {
        self.subtables.borrow_mut()
    }

    /// Returns the configuration used by this BDD manager.
    pub fn config(&self) -> &BddConfig {
        &self.config
    }

    /// Creates a new subtable for the given variable using the configured bucket bits.
    fn make_subtable(&self, var: Var) -> Subtable {
        Subtable::with_bucket_bits(var, self.config.subtable_bits)
    }

    /// Returns the number of allocated nodes (excluding free slots).
    pub fn num_nodes(&self) -> usize {
        // nodes.len() is the total number of nodes including terminal at index 0
        self.nodes().len() - self.free_set().len()
    }

    /// Returns a reference to the operation cache.
    pub fn cache(&self) -> cell::Ref<'_, Cache<OpKey, Ref>> {
        self.cache.borrow()
    }
    pub(crate) fn cache_mut(&self) -> cell::RefMut<'_, Cache<OpKey, Ref>> {
        self.cache.borrow_mut()
    }

    /// Returns a reference to the size computation cache.
    pub fn size_cache(&self) -> cell::Ref<'_, Cache<Ref, u64>> {
        self.size_cache.borrow()
    }
    pub(crate) fn size_cache_mut(&self) -> cell::RefMut<'_, Cache<Ref, u64>> {
        self.size_cache.borrow_mut()
    }
}

// ============================================================================
// Node data access
// ============================================================================

impl Bdd {
    /// Gets a copy of the node at the given index.
    pub fn node(&self, id: NodeId) -> Node {
        self.nodes()[id.index()]
    }

    /// Gets the variable of a node at the given index.
    pub fn variable(&self, id: NodeId) -> Var {
        self.node(id).variable
    }

    /// Gets the low child of a node.
    ///
    /// Returns the low edge of the node at the given index.
    pub fn low(&self, id: NodeId) -> Ref {
        self.node(id).low
    }

    /// Gets the high child of a node.
    ///
    /// Returns the high edge of the node at the given index.
    pub fn high(&self, id: NodeId) -> Ref {
        self.node(id).high
    }

    /// Gets the low child of a BDD node, respecting complement edges.
    ///
    /// If the node reference is negated, the returned child is also negated.
    /// This maintains the complement edge semantics throughout traversal.
    pub fn low_node(&self, node_ref: Ref) -> Ref {
        let low = self.low(node_ref.id());
        if node_ref.is_negated() {
            -low
        } else {
            low
        }
    }

    /// Gets the high child of a BDD node, respecting complement edges.
    ///
    /// If the node reference is negated, the returned child is also negated.
    /// This maintains the complement edge semantics throughout traversal.
    pub fn high_node(&self, node_ref: Ref) -> Ref {
        let high = self.high(node_ref.id());
        if node_ref.is_negated() {
            -high
        } else {
            high
        }
    }
}

// ============================================================================
// Terminal predicates
// ============================================================================

impl Bdd {
    /// Constant reference to the logical FALSE (0) node.
    ///
    /// **Note:** this is internally represented as `Ref(1)`, the negated node with index 0.
    pub const ZERO: Ref = Ref::negative(NodeId::TERMINAL);

    /// Constant reference to the logical TRUE (1) node.
    ///
    /// **Note:** this is internally represented as `Ref(0)`, the positive node with index 0.
    pub const ONE: Ref = Ref::positive(NodeId::TERMINAL);

    /// Returns the constant true BDD reference.
    ///
    /// This is the positive reference to the terminal node (index 0).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let one = bdd.one();
    /// assert!(bdd.is_one(one));
    /// ```
    #[inline]
    pub fn one(&self) -> Ref {
        Self::ONE
    }

    /// Returns the constant false BDD reference.
    ///
    /// This is the negated reference to the terminal node (index 0).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let zero = bdd.zero();
    /// assert!(bdd.is_zero(zero));
    /// ```
    #[inline]
    pub fn zero(&self) -> Ref {
        Self::ZERO
    }

    /// Checks if a BDD node represents the constant false.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// assert!(bdd.is_zero(bdd.zero()));
    /// assert!(!bdd.is_zero(bdd.one()));
    ///
    /// let x = bdd.mk_var(1);
    /// let contradiction = bdd.apply_and(x, -x);
    /// assert!(bdd.is_zero(contradiction));
    /// ```
    pub fn is_zero(&self, node_ref: Ref) -> bool {
        node_ref == self.zero()
    }

    /// Checks if a BDD node represents the constant true.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// assert!(bdd.is_one(bdd.one()));
    /// assert!(!bdd.is_one(bdd.zero()));
    ///
    /// let x = bdd.mk_var(1);
    /// let tautology = bdd.apply_or(x, -x);
    /// assert!(bdd.is_one(tautology));
    /// ```
    pub fn is_one(&self, node_ref: Ref) -> bool {
        node_ref == self.one()
    }

    /// Checks if a BDD node is a terminal (constant) node.
    ///
    /// Returns true if the node is either zero (false) or one (true).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// assert!(bdd.is_terminal(bdd.zero()));
    /// assert!(bdd.is_terminal(bdd.one()));
    ///
    /// let x = bdd.mk_var(1);
    /// assert!(!bdd.is_terminal(x));
    /// ```
    pub fn is_terminal(&self, node_ref: Ref) -> bool {
        node_ref.id() == NodeId::TERMINAL
    }
}

// ============================================================================
// Variable management
// ============================================================================

impl Bdd {
    /// Allocates a new variable and adds it to the end of the variable ordering.
    ///
    /// # Returns
    ///
    /// The newly allocated variable.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let var = bdd.allocate_variable();
    /// let x = bdd.mk_var(var);  // Can pass Var directly
    /// ```
    pub fn allocate_variable(&self) -> Var {
        let var_id = self.next_var_id.get();
        self.next_var_id.set(var_id + 1);

        let var = Var::new(var_id);
        let level = Level::new(self.var_order().len());

        self.var_order_mut().push(var);
        self.level_map_mut().insert(var, level);
        self.subtables_mut().push(self.make_subtable(var));

        var
    }

    /// Registers a variable in the ordering if it's not already present.
    ///
    /// This is called automatically by mk_var.
    fn register_variable(&self, var_id: u32) {
        let var = Var::new(var_id);

        if !self.level_map().contains_key(&var) {
            let level = Level::new(self.var_order().len());
            self.var_order_mut().push(var);
            self.level_map_mut().insert(var, level);
            self.subtables_mut().push(self.make_subtable(var));

            // Update next_var_id if needed
            let next_val = self.next_var_id.get();
            if var_id >= next_val {
                self.next_var_id.set(var_id + 1);
            }
        }
    }

    /// Returns true if var1 comes before var2 in the variable ordering.
    ///
    /// Uses the explicit variable ordering to compare levels.
    pub fn var_precedes(&self, var1: Var, var2: Var) -> bool {
        if var1.is_terminal() || var2.is_terminal() {
            return false;
        }

        let level1 = self.get_level(var1);
        let level2 = self.get_level(var2);

        match (level1, level2) {
            (Some(l1), Some(l2)) => l1 < l2,
            (Some(_), None) => true,
            (None, Some(_)) => false,
            (None, None) => var1.id() < var2.id(), // fallback to ID comparison
        }
    }

    /// Compare two variables by their level in the variable ordering.
    ///
    /// Terminal variables are considered greater than non-terminal variables.
    /// Both variables must be in the ordering; panics otherwise.
    pub fn var_cmp(&self, var1: Var, var2: Var) -> Ordering {
        if var1 == var2 {
            return Ordering::Equal;
        }
        if var1.is_terminal() {
            return Ordering::Greater;
        }
        if var2.is_terminal() {
            return Ordering::Less;
        }
        let level1 = self.get_level(var1).unwrap();
        let level2 = self.get_level(var2).unwrap();
        level1.cmp(&level2)
    }

    /// Compares two variables by their level in the variable ordering.
    ///
    /// Returns the variable that should appear *first* (at a lower level/higher in the tree).
    /// Uses the explicit variable ordering to determine precedence.
    ///
    /// # Arguments
    ///
    /// * `var1` - First variable (Var::ZERO means terminal/no variable)
    /// * `var2` - Second variable (Var::ZERO means terminal/no variable)
    ///
    /// # Returns
    ///
    /// The variable that comes first in the ordering, or Var::ZERO if both are terminals.
    pub fn top_variable(&self, var1: Var, var2: Var) -> Var {
        if var1.is_terminal() {
            return var2;
        }
        if var2.is_terminal() {
            return var1;
        }

        // var1 wins if it precedes var2, or on tie (same level)
        if self.var_precedes(var2, var1) {
            var2
        } else {
            var1
        }
    }
}

// ============================================================================
// Variable ordering
// ============================================================================

impl Bdd {
    /// Returns the current variable ordering as a vector.
    ///
    /// The i-th element is the variable at level i. Level 0 is the root level.
    pub fn get_variable_order(&self) -> Vec<Var> {
        self.var_order().clone()
    }

    /// Returns the variable at a given level, if it exists.
    pub fn get_variable_at_level(&self, level: Level) -> Option<Var> {
        self.var_order().get(level.index()).copied()
    }

    /// Returns the level of a variable in the current ordering.
    ///
    /// Returns `None` if the variable has not been registered.
    pub fn get_level(&self, var: Var) -> Option<Level> {
        self.level_map().get(&var).copied()
    }

    /// Returns all node indices at a specific level.
    ///
    /// This is primarily used internally for variable reordering.
    pub fn get_nodes_at_level(&self, level: Level) -> Vec<NodeId> {
        let nodes = self.nodes();
        self.subtables()
            .get(level.index())
            .map(|st| st.indices(&nodes).collect())
            .unwrap_or_default()
    }

    /// Returns the number of levels (registered variables) in the ordering.
    pub fn num_levels(&self) -> usize {
        self.var_order().len()
    }

    /// Sets the variable ordering for the BDD manager.
    ///
    /// This method should be called **before** creating any BDD nodes (other than
    /// terminal). It pre-allocates levels for the given variables in the specified
    /// order.
    ///
    /// # Arguments
    ///
    /// * `vars` - Variable IDs in the desired order (level 0 = first element)
    ///
    /// # Panics
    ///
    /// Panics if any BDD nodes have already been created (except the terminal node),
    /// or if duplicate variables are provided.
    ///
    /// # Example
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Define variable order: y (level 0) < x (level 1) < z (level 2)
    /// bdd.set_variable_order([2, 1, 3]);
    ///
    /// // Now create BDDs - variables will use the defined order
    /// let x = bdd.mk_var(1);  // x is at level 1
    /// let y = bdd.mk_var(2);  // y is at level 0 (root)
    /// let z = bdd.mk_var(3);  // z is at level 2
    ///
    /// assert_eq!(bdd.get_level(bdd.variable(y.id())).unwrap().index(), 0);
    /// assert_eq!(bdd.get_level(bdd.variable(x.id())).unwrap().index(), 1);
    /// assert_eq!(bdd.get_level(bdd.variable(z.id())).unwrap().index(), 2);
    /// ```
    pub fn set_variable_order(&self, vars: impl IntoIterator<Item = impl Into<Var>>) {
        // Check that no BDD nodes have been created yet
        assert!(
            self.num_nodes() == 1,
            "set_variable_order must be called before creating any BDD nodes"
        );
        assert!(self.var_order().is_empty(), "Variable order has already been set");

        let vars: Vec<Var> = vars.into_iter().map(|v| v.into()).collect();

        // Check for duplicates
        let mut seen = HashSet::new();
        for &var in &vars {
            assert!(seen.insert(var), "Duplicate variable in ordering: {:?}", var);
            assert!(!var.is_terminal(), "Terminal variable (0) cannot be in ordering");
        }

        // Set up the ordering
        let mut var_order = self.var_order_mut();
        let mut level_map = self.level_map_mut();
        let mut subtables = self.subtables_mut();

        for (level_idx, var) in vars.iter().enumerate() {
            let level = Level::new(level_idx);
            var_order.push(*var);
            level_map.insert(*var, level);
            subtables.push(Subtable::with_bucket_bits(*var, self.config.subtable_bits));
        }

        // Update next_var_id to be greater than any defined variable
        let max_var_id = vars.iter().map(|v| v.id()).max().unwrap_or(0);
        if max_var_id >= self.next_var_id.get() {
            self.next_var_id.set(max_var_id + 1);
        }
    }

    /// Applies a new variable ordering to an existing BDD by sifting variables.
    ///
    /// This method reorders variables in a BDD that already has nodes. It moves
    /// each variable to its target position using adjacent swaps, which preserves
    /// the represented Boolean function.
    ///
    /// # Arguments
    ///
    /// * `roots` - Mutable slice of BDD roots to update after reordering
    /// * `new_order` - Variable IDs in the desired order (level 0 = first element).
    ///   Variables not in `new_order` but present in the BDD will be moved to the end.
    ///
    /// # Returns
    ///
    /// Statistics about the reordering operation.
    ///
    /// # Example
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    /// let f = bdd.apply_and(x, bdd.apply_or(y, z));
    ///
    /// // Initial order: 1, 2, 3 (in allocation order)
    /// assert_eq!(bdd.get_variable_order(), vec![
    ///     ananke_bdd::types::Var::new(1),
    ///     ananke_bdd::types::Var::new(2),
    ///     ananke_bdd::types::Var::new(3)
    /// ]);
    ///
    /// // Apply new order: 3, 1, 2
    /// let mut roots = vec![f];
    /// bdd.apply_variable_order(&mut roots, [3u32, 1, 2]);
    ///
    /// assert_eq!(bdd.get_variable_order(), vec![
    ///     ananke_bdd::types::Var::new(3),
    ///     ananke_bdd::types::Var::new(1),
    ///     ananke_bdd::types::Var::new(2)
    /// ]);
    /// ```
    pub fn apply_variable_order(&self, roots: &mut [Ref], new_order: impl IntoIterator<Item = impl Into<Var>>) -> ReorderStats {
        let new_order: Vec<Var> = new_order.into_iter().map(|v| v.into()).collect();

        let initial_size = self.count_nodes(roots);
        let mut stats = ReorderStats {
            initial_size,
            final_size: initial_size,
            best_size: initial_size,
            swaps: 0,
            variables_processed: 0,
        };

        if new_order.is_empty() {
            return stats;
        }

        // Build target level for each variable
        let mut target_levels: HashMap<Var, Level> = HashMap::new();
        for (level_idx, var) in new_order.iter().enumerate() {
            target_levels.insert(*var, Level::new(level_idx));
        }

        // Move each variable to its target position, starting from the first
        // This is done by iterating through target levels and moving variables there
        for target_level_idx in 0..new_order.len() {
            let target_var = new_order[target_level_idx];
            let target_level = Level::new(target_level_idx);

            // Skip if variable is not in the BDD
            let Some(current_level) = self.get_level(target_var) else {
                continue;
            };

            if current_level != target_level {
                let swaps = self.move_variable_to_level(roots, target_var, target_level);
                stats.swaps += swaps;
                stats.variables_processed += 1;
            }
        }

        stats.final_size = self.count_nodes(roots);
        stats.best_size = stats.final_size.min(stats.best_size);
        stats
    }
}

// ============================================================================
// BDD construction
// ============================================================================

impl Bdd {
    /// Returns the constant false BDD.
    ///
    /// This is a convenience method equivalent to calling `bdd.zero()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let f = bdd.mk_false();
    /// assert!(bdd.is_zero(f));
    /// assert_eq!(f, bdd.zero());
    /// ```
    pub fn mk_false(&self) -> Ref {
        self.zero()
    }

    /// Returns the constant true BDD.
    ///
    /// This is a convenience method equivalent to calling `bdd.one()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let t = bdd.mk_true();
    /// assert!(bdd.is_one(t));
    /// assert_eq!(t, bdd.one());
    /// ```
    pub fn mk_true(&self) -> Ref {
        self.one()
    }

    /// Creates or retrieves a BDD node with the given variable and children.
    ///
    /// This is the fundamental node constructor that enforces all BDD invariants:
    /// - **Canonicity**: High edge is never complemented (negates entire node if needed)
    /// - **Reduction**: If low == high, returns the child directly (no redundant node)
    /// - **Uniqueness**: Uses hash consing to return existing identical nodes
    ///
    /// # Arguments
    ///
    /// * `v` - The decision variable (must not be terminal)
    /// * `low` - Child followed when `v` is false
    /// * `high` - Child followed when `v` is true
    ///
    /// # Returns
    ///
    /// A reference to the (possibly existing) node. May be negated if canonicity
    /// required flipping the node.
    ///
    /// # Panics
    ///
    /// Panics if `v` is the terminal variable (`Var::ZERO`).
    ///
    /// # Invariants Enforced
    ///
    /// 1. High edge is always positive (complement only on low edge)
    /// 2. Redundant nodes eliminated (low == high → return child)
    /// 3. Identical nodes shared (hash consing)
    pub fn mk_node(&self, v: Var, low: Ref, high: Ref) -> Ref {
        // debug!("mk(v = {}, low = {}, high = {})", v, low, high);

        assert!(!v.is_terminal(), "Variable must not be Var::ZERO");

        // Handle canonicity
        if high.is_negated() {
            // debug!("mk: restoring canonicity");
            return -self.mk_node(v, -low, -high);
        }

        // Handle duplicates
        if low == high {
            // debug!("mk: duplicates {} == {}", low, high);
            return low;
        }

        // Auto-register the variable if needed
        self.register_variable(v.id());

        // Get the level for this variable (guaranteed to exist now)
        let level = self.get_level(v).expect("Variable should be registered");

        // Check if node exists in subtable (needs read access to nodes for chain traversal)
        if let Some(id) = self.subtables()[level.index()].find(low, high, &self.nodes()) {
            return Ref::positive(id);
        }

        // Node doesn't exist - allocate and insert
        let node = Node::new(v, low, high);
        let id = {
            let mut free_set = self.free_set_mut();
            if let Some(&id) = free_set.iter().next() {
                free_set.remove(&id);
                // Reuse a freed slot
                self.nodes_mut()[id.index()] = node;
                id
            } else {
                // Allocate new slot
                let mut nodes = self.nodes_mut();
                let id = NodeId::new(nodes.len() as u32);
                nodes.push(node);
                id
            }
        };

        // Insert into subtable (needs mutable access to nodes for setting next pointer)
        self.subtables_mut()[level.index()].insert_with_resize(low, high, id, &mut self.nodes_mut());

        Ref::positive(id)
    }

    /// Creates a BDD representing a single Boolean variable.
    ///
    /// Returns a BDD that is true when the variable is true and false otherwise.
    /// This is the primary way to introduce variables into BDD expressions.
    ///
    /// # Arguments
    ///
    /// * `v` - Variable (must not be terminal). Can be a `Var` or `u32`.
    ///
    /// # Panics
    ///
    /// Panics if `v` is the terminal variable (`Var::ZERO`) or if passing `0u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Using raw integers
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    ///
    /// // Using Var type
    /// let x3 = bdd.mk_var(Var::new(3));
    ///
    /// // Using allocate_variable (returns Var)
    /// let x4 = bdd.allocate_variable();
    /// let bdd_x4 = bdd.mk_var(x4);
    ///
    /// // Variables can be negated
    /// let not_x1 = -x1;
    ///
    /// // And combined with operations
    /// let f = bdd.apply_and(x1, x2);
    /// ```
    pub fn mk_var(&self, v: impl Into<Var>) -> Ref {
        let v = v.into();
        assert!(!v.is_terminal(), "Variable must not be terminal");

        // Register variable in ordering
        self.register_variable(v.id());

        self.mk_node(v, self.zero(), self.one())
    }

    /// Creates a BDD representing a conjunction (AND) of literals.
    ///
    /// A cube is a conjunction of positive or negative literals.
    /// This is more efficient than manually creating multiple AND operations.
    ///
    /// # Arguments
    ///
    /// * `literals` - Iterator of literals. Each literal can be:
    ///   - A `Lit` (type-safe literal)
    ///   - An `i32` (DIMACS-style: positive = positive literal, negative = negated)
    ///
    /// # Returns
    ///
    /// A BDD representing the conjunction of all literals.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::{Var, Lit};
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Using i32 (DIMACS-style, backward compatible)
    /// let cube1 = bdd.mk_cube([1, -2, 3]);
    ///
    /// // Using Lit (type-safe) - produces identical result
    /// let x1 = Var::new(1);
    /// let x2 = Var::new(2);
    /// let x3 = Var::new(3);
    /// let cube2 = bdd.mk_cube([x1.pos(), x2.neg(), x3.pos()]);
    ///
    /// assert_eq!(cube1, cube2);
    /// ```
    pub fn mk_cube(&self, literals: impl IntoIterator<Item = impl Into<Lit>>) -> Ref {
        let mut literals: Vec<Lit> = literals.into_iter().map(|l| l.into()).collect();
        debug!("cube(literals = {:?})", literals);

        // First, register all variables to ensure they all have levels
        for lit in &literals {
            self.register_variable(lit.var().id());
        }

        // Sort with respect to the variable ordering
        literals.sort_unstable_by(|a, b| self.var_cmp(a.var(), b.var()));

        // Now reverse and build bottom-up
        literals.reverse();
        let mut current = self.one();
        for lit in literals {
            let var = lit.var();
            current = if lit.is_negative() {
                self.mk_node(var, current, self.zero())
            } else {
                self.mk_node(var, self.zero(), current)
            };
        }
        current
    }

    /// Creates a BDD representing a disjunction (OR) of literals.
    ///
    /// A clause is a disjunction of positive or negative literals.
    /// This is more efficient than manually creating multiple OR operations.
    ///
    /// # Arguments
    ///
    /// * `literals` - Iterator of literals. Each literal can be:
    ///   - A `Lit` (type-safe literal)
    ///   - An `i32` (DIMACS-style: positive = positive literal, negative = negated)
    ///
    /// # Returns
    ///
    /// A BDD representing the disjunction of all literals.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::{Var, Lit};
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Using i32 (DIMACS-style, backward compatible)
    /// let clause1 = bdd.mk_clause([1, -2, 3]);
    ///
    /// // Using Lit (type-safe)
    /// let x1 = Var::new(1);
    /// let x2 = Var::new(2);
    /// let x3 = Var::new(3);
    /// let clause2 = bdd.mk_clause([x1.pos(), x2.neg(), x3.pos()]);
    ///
    /// assert_eq!(clause1, clause2);
    /// ```
    pub fn mk_clause(&self, literals: impl IntoIterator<Item = impl Into<Lit>>) -> Ref {
        let mut literals: Vec<Lit> = literals.into_iter().map(|l| l.into()).collect();
        debug!("clause(literals = {:?})", literals);

        // First, register all variables to ensure they all have levels
        for lit in &literals {
            self.register_variable(lit.var().id());
        }

        // Sort with respect to the variable ordering
        literals.sort_unstable_by(|a, b| self.var_cmp(a.var(), b.var()));

        // Now reverse and build bottom-up
        literals.reverse();
        let mut current = self.zero();
        for lit in literals {
            let var = lit.var();
            current = if lit.is_negative() {
                self.mk_node(var, self.one(), current)
            } else {
                self.mk_node(var, current, self.one())
            };
        }
        current
    }
}

// ============================================================================
// Boolean operations (apply_*)
// ============================================================================

impl Bdd {
    /// Returns the top cofactors (Shannon expansion) with respect to a variable.
    ///
    /// For a BDD `f` and variable `v`, returns `(f₀, f₁)` where:
    /// - `f₀` is the negative cofactor (`f` with `v = false`)
    /// - `f₁` is the positive cofactor (`f` with `v = true`)
    ///
    /// This corresponds to the Shannon expansion: `f = (¬v ∧ f₀) ∨ (v ∧ f₁)`
    ///
    /// # Parameters
    ///
    /// * `node_ref` - The BDD to compute cofactors for
    /// * `v` - Variable (must be non-zero and ≤ top variable of `node_ref`)
    ///
    /// # Returns
    ///
    /// A tuple `(f₀, f₁)` of the negative and positive cofactors.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x AND y
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Cofactors with respect to x
    /// let (f0, f1) = bdd.top_cofactors(f, Var::new(1));
    /// assert_eq!(f0, bdd.zero());  // x=false: false AND y = false
    /// assert_eq!(f1, y);         // x=true: true AND y = y
    /// ```
    pub fn top_cofactors(&self, node_ref: Ref, v: Var) -> (Ref, Ref) {
        assert!(!v.is_terminal(), "Variable must not be Var::ZERO");

        if self.is_terminal(node_ref) {
            return (node_ref, node_ref);
        }

        let id = node_ref.id();
        let node = self.node(id);

        // Check if v comes before node.variable in the ordering
        if self.var_precedes(v, node.variable) {
            // 'node' does not depend on 'v' (v is at a higher level, not in this subtree)
            return (node_ref, node_ref);
        }
        assert_eq!(v, node.variable);
        if node_ref.is_negated() {
            (-node.low, -node.high)
        } else {
            (node.low, node.high)
        }
    }

    /// Apply the ITE operation to the arguments.
    ///
    /// ```text
    /// ITE(x, y, z) == (x ∧ y) ∨ (¬x ∧ z) == (x -> y) ∧ (¬x -> z)
    /// ```
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    /// let f = bdd.apply_ite(x, y, z);
    /// assert_eq!(f, bdd.mk_node(bdd.variable(x.id()), z, y));
    /// let  x_and_y = bdd.apply_and(x, y);
    /// let  not_x_and_z = bdd.apply_and(-x, z);
    /// assert_eq!(f, bdd.apply_or(x_and_y, not_x_and_z));
    /// ```
    pub fn apply_ite(&self, f: Ref, g: Ref, h: Ref) -> Ref {
        debug!("apply_ite(f = {}, g = {}, h = {})", f, g, h);

        // Base cases:
        //   ite(1,G,H) => G
        //   ite(0,G,H) => H
        if self.is_one(f) {
            debug!("ite(1,G,H) => G");
            return g;
        }
        if self.is_zero(f) {
            debug!("ite(0,G,H) => H");
            return h;
        }

        // From now on, F is known not to be a constant
        assert!(!self.is_terminal(f));

        // More base cases:
        //   ite(F,G,G) => G
        //   ite(F,1,0) => F
        //   ite(F,0,1) => ~F
        //   ite(F,1,~F) => 1
        //   ite(F,F,1) => 1
        //   ite(F,~F,0) => 0
        //   ite(F,0,F) => F
        if g == h {
            debug!("ite(F,G,G) => G");
            return g;
        }
        if self.is_one(g) && self.is_zero(h) {
            debug!("ite(F,1,0) => F");
            return f;
        }
        if self.is_zero(g) && self.is_one(h) {
            debug!("ite(F,0,1) => ~F");
            return -f;
        }
        if self.is_one(g) && h == -f {
            debug!("ite(F,1,~F) => 1");
            return self.one();
        }
        if g == f && self.is_one(h) {
            debug!("ite(F,F,1) => 1");
            return self.one();
        }
        if g == -f && self.is_zero(h) {
            debug!("ite(F,~F,0) => 0");
            return self.zero();
        }
        if self.is_zero(g) && h == f {
            debug!("ite(F,0,F) => F");
            return f;
        }

        // Standard triples:
        //   ite(F,F,H) => ite(F,1,H)
        //   ite(F,G,F) => ite(F,G,0)
        //   ite(F,~F,H) => ite(F,0,H)
        //   ite(F,G,~F) => ite(F,G,1)
        if g == f {
            debug!("ite(F,F,H) => ite(F,1,H)");
            return self.apply_ite(f, self.one(), h);
        }
        if h == f {
            debug!("ite(F,G,F) => ite(F,G,0)");
            return self.apply_ite(f, g, self.zero());
        }
        if g == -f {
            debug!("ite(F,~F,H) => ite(F,0,H)");
            return self.apply_ite(f, self.zero(), h);
        }
        if h == -f {
            debug!("ite(F,G,~F) => ite(F,G,1)");
            return self.apply_ite(f, g, self.one());
        }

        let i = self.variable(f.id());
        let j = self.variable(g.id());
        let k = self.variable(h.id());
        assert!(!i.is_terminal());

        // Equivalent pairs:
        //   ite(F,1,H) == ite(H,1,F) == F ∨ H
        //   ite(F,G,0) == ite(G,F,0) == F ∧ G
        //   ite(F,G,1) == ite(~G,~F,1) == F -> G
        //   ite(F,0,H) == ite(~H,0,~F) == ~F ∧ H
        //   ite(F,G,~G) == ite(G,F,~F)
        // (choose the one with the lowest variable)
        if self.is_one(g) && self.var_precedes(k, i) {
            assert!(!k.is_terminal());
            debug!("ite(F,1,H) => ite(H,1,F)");
            return self.apply_ite(h, self.one(), f);
        }
        if self.is_zero(h) && self.var_precedes(j, i) {
            assert!(!j.is_terminal());
            debug!("ite(F,G,0) => ite(G,F,0)");
            return self.apply_ite(g, f, self.zero());
        }
        if self.is_one(h) && self.var_precedes(j, i) {
            assert!(!j.is_terminal());
            debug!("ite(F,G,1) => ite(~G,~F,1)");
            return self.apply_ite(-g, -f, self.one());
        }
        if self.is_zero(g) && self.var_precedes(k, i) {
            assert!(!k.is_terminal());
            debug!("ite(F,0,H) => ite(~H,0,~F)");
            return self.apply_ite(-h, self.zero(), -f);
        }
        if g == -h && self.var_precedes(j, i) {
            assert!(!j.is_terminal());
            debug!("ite(F,G,~G) => ite(G,F,~F)");
            return self.apply_ite(g, f, -f);
        }

        // Make sure the first two pointers (f and g) are regular (not negated)
        let (mut f, mut g, mut h) = (f, g, h);

        // ite(~F,G,H) => ite(F,H,G)
        if f.is_negated() {
            debug!("ite(~F,G,H) => ite(F,H,G)");
            f = -f;
            std::mem::swap(&mut g, &mut h);
        }
        assert!(!f.is_negated());

        // ite(F,~G,H) => ~ite(F,G,~H)
        let mut n = false;
        if g.is_negated() {
            n = true;
            g = -g;
            h = -h;
        }
        assert!(!g.is_negated());

        let (f, g, h) = (f, g, h); // make immutable

        let key = OpKey::Ite(f, g, h);
        debug!("key = {:?}", key);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: apply_ite(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
            return if n { -res } else { res };
        }

        // Determine the top variable:
        let mut m = i;
        if !j.is_terminal() {
            m = self.top_variable(m, j);
        }
        if !k.is_terminal() {
            m = self.top_variable(m, k);
        }
        debug!("top variable = {}", m);
        assert!(!m.is_terminal());

        let (f0, f1) = self.top_cofactors(f, m);
        debug!("cofactors of f = {} are: f0 = {}, f1 = {}", f, f0, f1);
        let (g0, g1) = self.top_cofactors(g, m);
        debug!("cofactors of g = {} are: g0 = {}, g1 = {}", g, g0, g1);
        let (h0, h1) = self.top_cofactors(h, m);
        debug!("cofactors of h = {} are: h0 = {}, h1 = {}", h, h0, h1);

        let e = self.apply_ite(f0, g0, h0);
        let t = self.apply_ite(f1, g1, h1);
        debug!("cofactors of res: e = {}, t = {}", e, t);

        let res = self.mk_node(m, e, t);
        debug!("computed: apply_ite(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
        self.cache_mut().insert(key, res);
        if n {
            -res
        } else {
            res
        }
    }

    fn maybe_constant(&self, node_ref: Ref) -> Option<bool> {
        if self.is_zero(node_ref) {
            Some(false)
        } else if self.is_one(node_ref) {
            Some(true)
        } else {
            None
        }
    }

    /// Checks if `ITE(f, g, h)` evaluates to a constant without building the BDD.
    ///
    /// Returns:
    /// - `Some(true)` if the result is always true (ONE)
    /// - `Some(false)` if the result is always false (ZERO)
    /// - `None` if the result depends on variable assignments
    ///
    /// This is useful for implication checking and other queries where we only
    /// care if the result is constant, not the full BDD structure.
    pub fn ite_constant(&self, f: Ref, g: Ref, h: Ref) -> Option<bool> {
        debug!("ite_constant(f = {}, g = {}, h = {})", f, g, h);

        // TODO: "trivial" cases

        // Base cases:
        //   ite(1,G,H) => G
        //   ite(0,G,H) => H
        if self.is_one(f) {
            debug!("ite(1,G,H) => G");
            // return g;
            return self.maybe_constant(g);
        }
        if self.is_zero(f) {
            debug!("ite(0,G,H) => H");
            // return h;
            return self.maybe_constant(h);
        }

        // From now on, F is known not to be a constant
        assert!(!self.is_terminal(f));

        // More base cases:
        //   ite(F,G,G) => G
        //   ite(F,1,0) => F
        //   ite(F,0,1) => ~F
        //   ite(F,1,~F) => 1
        //   ite(F,F,1) => 1
        //   ite(F,~F,0) => 0
        //   ite(F,0,F) => F
        if g == h {
            debug!("ite(F,G,G) => G");
            // return g;
            return self.maybe_constant(g);
        }
        if self.is_one(g) && self.is_zero(h) {
            debug!("ite(F,1,0) => F");
            // return f;
            return None;
        }
        if self.is_zero(g) && self.is_one(h) {
            debug!("ite(F,0,1) => ~F");
            // return -f;
            return None;
        }
        if self.is_one(g) && h == -f {
            debug!("ite(F,1,~F) => 1");
            // return self.one;
            return Some(true);
        }
        if g == f && self.is_one(h) {
            debug!("ite(F,F,1) => 1");
            // return self.one;
            return Some(true);
        }
        if g == -f && self.is_zero(h) {
            debug!("ite(F,~F,0) => 0");
            // return self.zero;
            return Some(false);
        }
        if self.is_zero(g) && h == f {
            debug!("ite(F,0,F) => F");
            // return f;
            return None;
        }

        // TODO: standard triples?

        let key = OpKey::Ite(f, g, h);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: ite_constant(f = {}, g = {}, h = {}) -> {}", f, g, h, res);
            assert!(!self.is_terminal(res));
            return None;
        }

        let i = self.variable(f.id());
        let j = self.variable(g.id());
        let k = self.variable(h.id());
        assert!(!i.is_terminal());

        // Determine the top variable:
        let mut m = i;
        if !j.is_terminal() {
            m = self.top_variable(m, j);
        }
        if !k.is_terminal() {
            m = self.top_variable(m, k);
        }
        debug!("top variable = {}", m);
        assert!(!m.is_terminal());

        let (f0, f1) = self.top_cofactors(f, m);
        debug!("cofactors of f = {} are: f0 = {}, f1 = {}", f, f0, f1);
        let (g0, g1) = self.top_cofactors(g, m);
        debug!("cofactors of g = {} are: g0 = {}, g1 = {}", g, g0, g1);
        let (h0, h1) = self.top_cofactors(h, m);
        debug!("cofactors of h = {} are: h0 = {}, h1 = {}", h, h0, h1);

        let t = self.ite_constant(f1, g1, h1);
        if t.is_none() {
            return None;
        }
        let e = self.ite_constant(f0, g0, h0);
        if e != Some(true) {
            return None;
        }
        t
    }

    /// Checks if `f` logically implies `g` (i.e., `f → g` is a tautology).
    ///
    /// Returns `true` if for all assignments where `f` is true, `g` is also true.
    /// Equivalent to checking if `f ∧ ¬g` is unsatisfiable.
    ///
    /// This is more efficient than building the implication BDD and checking if it's ONE,
    /// as it can short-circuit when the result is determined.
    pub fn is_implies(&self, f: Ref, g: Ref) -> bool {
        debug!("is_implies(f = {}, g = {})", f, g);
        self.ite_constant(f, g, self.one()) == Some(true)
    }

    /// Returns the negation of a BDD in O(1) time.
    ///
    /// Complement edges make negation trivial: just flip the complement bit.
    /// No new nodes are created.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let not_x = bdd.apply_not(x);
    ///
    /// // Equivalent to unary negation
    /// assert_eq!(not_x, -x);
    ///
    /// // Double negation
    /// assert_eq!(bdd.apply_not(not_x), x);
    /// ```
    pub fn apply_not(&self, f: Ref) -> Ref {
        debug!("apply_not(f = {})", f);
        -f
    }

    /// Computes the conjunction (AND) of two BDDs: `u ∧ v`.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let and = bdd.apply_and(x, y);
    ///
    /// // AND is commutative
    /// assert_eq!(bdd.apply_and(x, y), bdd.apply_and(y, x));
    ///
    /// // AND with constants
    /// assert_eq!(bdd.apply_and(x, bdd.one()), x);
    /// assert!(bdd.is_zero(bdd.apply_and(x, bdd.zero())));
    /// ```
    pub fn apply_and(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_and(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.zero())
    }

    /// Computes the disjunction (OR) of two BDDs: `u ∨ v`.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let or = bdd.apply_or(x, y);
    ///
    /// // OR is commutative
    /// assert_eq!(bdd.apply_or(x, y), bdd.apply_or(y, x));
    ///
    /// // OR with constants
    /// assert_eq!(bdd.apply_or(x, bdd.zero()), x);
    /// assert!(bdd.is_one(bdd.apply_or(x, bdd.one())));
    /// ```
    pub fn apply_or(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_or(u = {}, v = {})", u, v);
        self.apply_ite(u, self.one(), v)
    }

    /// Computes the exclusive OR (XOR) of two BDDs: `u ⊕ v`.
    ///
    /// True when exactly one operand is true.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let xor = bdd.apply_xor(x, y);
    ///
    /// // XOR is commutative
    /// assert_eq!(bdd.apply_xor(x, y), bdd.apply_xor(y, x));
    ///
    /// // XOR with itself is false
    /// assert!(bdd.is_zero(bdd.apply_xor(x, x)));
    ///
    /// // XOR is equivalent to inequality
    /// let neq = bdd.apply_and(bdd.apply_or(x, y), bdd.apply_not(bdd.apply_and(x, y)));
    /// assert_eq!(xor, neq);
    /// ```
    pub fn apply_xor(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_xor(u = {}, v = {})", u, v);
        self.apply_ite(u, -v, v)
    }

    /// Computes the equivalence (XNOR) of two BDDs: `u <=> v`.
    ///
    /// True when both operands have the same value.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let eq = bdd.apply_eq(x, y);
    ///
    /// // Equivalence with itself is true
    /// assert!(bdd.is_one(bdd.apply_eq(x, x)));
    ///
    /// // Equivalence is the negation of XOR
    /// assert_eq!(eq, bdd.apply_not(bdd.apply_xor(x, y)));
    /// ```
    pub fn apply_eq(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_eq(u = {}, v = {})", u, v);
        self.apply_ite(u, v, -v)
    }

    /// Computes the implication of two BDDs: `u -> v`.
    ///
    /// Equivalent to `¬u ∨ v`.
    ///
    /// Implemented using [`apply_ite`](Bdd::apply_ite).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// let implies = bdd.apply_imply(x, y);
    ///
    /// // x implies x is always true
    /// assert!(bdd.is_one(bdd.apply_imply(x, x)));
    ///
    /// // Equivalent to NOT x OR y
    /// let equivalent = bdd.apply_or(-x, y);
    /// assert_eq!(implies, equivalent);
    /// ```
    pub fn apply_imply(&self, u: Ref, v: Ref) -> Ref {
        debug!("apply_imply(u = {}, v = {})", u, v);
        self.apply_ite(u, v, self.one())
    }

    /// Computes the conjunction (AND) of multiple BDDs.
    ///
    /// More convenient than chaining multiple [`apply_and`](Bdd::apply_and) calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // AND of multiple variables
    /// let and_all = bdd.apply_and_many([x, y, z]);
    ///
    /// // Equivalent to:
    /// let manual = bdd.apply_and(bdd.apply_and(x, y), z);
    /// assert_eq!(and_all, manual);
    ///
    /// // Also equivalent to cube
    /// assert_eq!(and_all, bdd.mk_cube([1, 2, 3]));
    /// ```
    pub fn apply_and_many(&self, nodes: impl IntoIterator<Item = Ref>) -> Ref {
        debug!("apply_and_many(...)");
        let mut res = self.one();
        for node_ref in nodes.into_iter() {
            res = self.apply_and(res, node_ref);
        }
        res
    }

    /// Computes the disjunction (OR) of multiple BDDs.
    ///
    /// More convenient than chaining multiple [`apply_or`](Bdd::apply_or) calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // OR of multiple variables
    /// let or_all = bdd.apply_or_many([x, y, z]);
    ///
    /// // Equivalent to:
    /// let manual = bdd.apply_or(bdd.apply_or(x, y), z);
    /// assert_eq!(or_all, manual);
    ///
    /// // Also equivalent to clause
    /// assert_eq!(or_all, bdd.mk_clause([1, 2, 3]));
    /// ```
    pub fn apply_or_many(&self, nodes: impl IntoIterator<Item = Ref>) -> Ref {
        debug!("apply_or_many(...)");
        let mut res = self.zero();
        for node_ref in nodes.into_iter() {
            res = self.apply_or(res, node_ref);
        }
        res
    }
}

// ============================================================================
// Substitution and composition
// ============================================================================

impl Bdd {
    /// Substitutes a variable with a Boolean constant.
    ///
    /// Returns a new BDD where all occurrences of variable `v` are replaced with
    /// the constant `b`. This is also called the cofactor operation.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to substitute in
    /// * `v` - Variable to substitute (must be non-zero)
    /// * `b` - Boolean value to substitute (true or false)
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = (x = y) ∨ x
    /// let f = bdd.apply_or(bdd.apply_eq(x, y), x);
    ///
    /// // Substitute x with true (using raw integer)
    /// // f[x<-1] = (1 = y) ∨ 1  ==>  1
    /// let f_x_true = bdd.substitute(f, 1, true);
    /// assert!(bdd.is_one(f_x_true)); // Result is always true
    ///
    /// // Substitute y with false (using Var)
    /// // f[y<-0] = (x = 0) ∨ x  ==>  1
    /// let f_y_false = bdd.substitute(f, Var::new(2), false);
    /// assert!(bdd.is_one(f_y_false)); // Result is always true
    /// ```
    // f|v<-b
    pub fn substitute(&self, f: Ref, v: impl Into<Var>, b: bool) -> Ref {
        let v = v.into();
        let mut cache = HashMap::new();
        self.substitute_(f, v, b, &mut cache)
    }

    fn substitute_(&self, f: Ref, v: Var, b: bool, cache: &mut HashMap<Ref, Ref>) -> Ref {
        assert!(!v.is_terminal(), "Variable must not be terminal");

        if self.is_terminal(f) {
            return f;
        }

        let i = self.variable(f.id());

        if self.var_precedes(v, i) {
            // 'v' comes before 'i' in ordering, so 'f' does not depend on 'v'
            return f;
        }

        if v == i {
            // Note: here, we do not need to wrap it with restrict(...).
            return if b { self.high_node(f) } else { self.low_node(f) };
        }

        if let Some(&res) = cache.get(&f) {
            return res;
        }

        assert!(self.var_precedes(i, v));
        let low = self.substitute_(self.low_node(f), v, b, cache);
        let high = self.substitute_(self.high_node(f), v, b, cache);
        let res = self.mk_node(i, low, high);
        cache.insert(f, res);
        res
    }

    /// Substitutes multiple variables with boolean values simultaneously.
    ///
    /// This is equivalent to applying [`substitute`](Bdd::substitute) multiple times,
    /// but more efficient as it performs all substitutions in a single traversal.
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to substitute variables in
    /// * `values` - A map from variable indices to their boolean values
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    /// use std::collections::HashMap;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_and(x, y);
    ///
    /// let mut values = HashMap::new();
    /// values.insert(Var::new(1), true);  // x = true
    /// values.insert(Var::new(2), false); // y = false
    ///
    /// let result = bdd.substitute_multi(f, &values);
    /// assert_eq!(result, bdd.zero()); // true AND false = false
    /// ```
    pub fn substitute_multi(&self, f: Ref, values: &HashMap<Var, bool>) -> Ref {
        let mut cache = HashMap::new();
        self.substitute_multi_(f, values, &mut cache)
    }

    fn substitute_multi_(&self, f: Ref, values: &HashMap<Var, bool>, cache: &mut HashMap<Ref, Ref>) -> Ref {
        debug!("restrict_multi(f = {}, values = {:?})", f, values);

        if self.is_terminal(f) {
            return f;
        }

        if values.is_empty() {
            return f;
        }

        if let Some(&res) = cache.get(&f) {
            return res;
        }

        let i = self.variable(f.id());
        let res = if let Some(&b) = values.get(&i) {
            if b {
                // `i` needs to be assigned true
                self.substitute_multi_(self.high_node(f), values, cache)
            } else {
                // `i` needs to be assigned false
                self.substitute_multi_(self.low_node(f), values, cache)
            }
        } else {
            // `i` does not need to be assigned
            let low = self.substitute_multi_(self.low_node(f), values, cache);
            let high = self.substitute_multi_(self.high_node(f), values, cache);
            self.mk_node(i, low, high)
        };
        cache.insert(f, res);
        res
    }

    /// Computes the cofactor of a BDD with respect to a cube.
    ///
    /// A cube is a conjunction of literals. This operation substitutes each
    /// variable in the cube with its corresponding value (positive = true, negative = false).
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to cofactor
    /// * `cube` - Literals representing the cube (positive for true, negative for false)
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::{Var, Lit};
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_or(x, y);
    ///
    /// // Cofactor with respect to x=true, y=false (using DIMACS-style integers)
    /// let result = bdd.cofactor_cube(f, [1, -2]);
    /// assert_eq!(result, bdd.one()); // true OR false = true
    ///
    /// // Or using Lit type directly
    /// let result = bdd.cofactor_cube(f, [Var::new(1).pos(), Var::new(2).neg()]);
    /// assert_eq!(result, bdd.one());
    /// ```
    pub fn cofactor_cube(&self, f: Ref, cube: impl IntoIterator<Item = impl Into<Lit>>) -> Ref {
        // Filter out variables not in the ordering and sort by level
        let mut lits: Vec<Lit> = cube
            .into_iter()
            .map(|l| l.into())
            .filter(|lit| self.get_level(lit.var()).is_some())
            .collect();
        lits.sort_unstable_by(|a, b| self.var_cmp(a.var(), b.var()));
        let mut cache = HashMap::new();
        self.cofactor_cube_(f, &lits, &mut cache)
    }

    fn cofactor_cube_(&self, f: Ref, cube: &[Lit], cache: &mut HashMap<(usize, Ref), Ref>) -> Ref {
        if cube.is_empty() {
            return f;
        }

        if self.is_terminal(f) {
            return f;
        }

        let key = (cube.len(), f);
        if let Some(&res) = cache.get(&key) {
            return res;
        }

        let t = self.variable(f.id()); // top variable of `f`
        let lit = cube[0];
        let u = lit.var();

        // Both t and u must have levels:
        // - t is in the BDD, so it must have a level
        // - u was pre-filtered to only include variables with levels
        let Some(tl) = self.get_level(t) else {
            unreachable!("BDD variable {} must have a level", t);
        };
        let Some(ul) = self.get_level(u) else {
            unreachable!("Cube variable {} must have a level", u);
        };

        let res = match tl.cmp(&ul) {
            Ordering::Greater => {
                // `t` is at a greater (lower) level than `u`, so `f` doesn't depend on `u`
                self.cofactor_cube_(f, &cube[1..], cache)
            }
            Ordering::Equal => {
                // `t == u`: `u` is the top variable of `f`
                let branch = if lit.is_positive() { self.high_node(f) } else { self.low_node(f) };
                self.cofactor_cube_(branch, &cube[1..], cache)
            }
            Ordering::Less => {
                // `t` is at a smaller (higher) level than `u`
                let f0 = self.low_node(f);
                let f1 = self.high_node(f);
                let low = self.cofactor_cube_(f0, cube, cache);
                let high = self.cofactor_cube_(f1, cube, cache);
                self.mk_node(t, low, high)
            }
        };
        cache.insert(key, res);
        res
    }

    /// Composes a BDD by substituting a variable with another BDD: `f|v<-g`.
    ///
    /// Returns a new BDD where all occurrences of variable `v` in `f` are replaced
    /// with the BDD `g`. This is also known as functional composition.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to compose
    /// * `v` - Variable to substitute (must not be terminal)
    /// * `g` - BDD to substitute for the variable
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // f = x AND z
    /// let f = bdd.apply_and(x, z);
    ///
    /// // Replace x with (y XOR z) - using raw integer
    /// let g = bdd.apply_xor(y, z);
    /// let result = bdd.compose(f, 1, g);
    ///
    /// // Or using Var type
    /// let result = bdd.compose(f, Var::new(1), g);
    ///
    /// // Result is (y XOR z) AND z, which simplifies to (NOT y AND z)
    /// ```
    pub fn compose(&self, f: Ref, v: impl Into<Var>, g: Ref) -> Ref {
        let v = v.into();
        let mut cache = Cache::new(16);
        self.compose_(f, v, g, &mut cache)
    }

    fn compose_(&self, f: Ref, v: Var, g: Ref, cache: &mut Cache<(Ref, Ref), Ref>) -> Ref {
        // TODO: compose(f, v, g) = ITE(g, restrict(f, v, true), restrict(f, v, false))

        debug!("compose(f = {}, v = {}, g = {})", f, v, g);

        if self.is_terminal(f) {
            return f;
        }

        let i = self.variable(f.id());
        assert!(!i.is_terminal());
        if self.var_precedes(v, i) {
            // 'v' comes before 'i' in ordering, so 'f' does not depend on 'v'
            return f;
        }

        let key = (f, g);
        if let Some(&res) = cache.get(&key) {
            return res;
        }

        let res = if v == i {
            let node = self.node(f.id());
            let res = self.apply_ite(g, node.high, node.low);
            if f.is_negated() {
                -res
            } else {
                res
            }
        } else {
            assert!(self.var_precedes(i, v));

            let m = if self.is_terminal(g) {
                i
            } else {
                self.top_variable(i, self.variable(g.id()))
            };
            assert!(!m.is_terminal());

            let (f0, f1) = self.top_cofactors(f, m);
            let (g0, g1) = self.top_cofactors(g, m);
            let h0 = self.compose_(f0, v, g0, cache);
            let h1 = self.compose_(f1, v, g1, cache);

            self.mk_node(m, h0, h1)
        };
        cache.insert(key, res);
        res
    }

    /// Computes the generalized cofactor (constrain operator): `f|g`.
    ///
    /// The constrain operator restricts function `f` to the domain where `g` is true,
    /// simplifying `f` while preserving its behavior on inputs satisfying `g`.
    /// This is also known as the *generalized cofactor* of `f` with respect to `g`.
    ///
    /// # Mathematical Definition
    ///
    /// The constrain operator `f|g` is defined as:
    /// - `f|1 = f` (no restriction)
    /// - `f|0 = 0` (empty domain)
    /// - `f|g` simplifies `f` by assuming `g` is true
    ///
    /// For any assignment where `g = 1`, we have `(f|g) = f`.
    /// For assignments where `g = 0`, the value of `(f|g)` is don't-care.
    ///
    /// # Properties
    ///
    /// - `f|1 = f`
    /// - `f|0 = 0`
    /// - `f|f = 1`
    /// - `f|~f = 0`
    /// - If `f` is a terminal, `f|g = f`
    ///
    /// # Parameters
    ///
    /// * `f` - The function to be constrained
    /// * `g` - The constraint (domain restriction)
    ///
    /// # Returns
    ///
    /// A BDD reference representing `f|g` (f constrained by g).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    ///
    /// // Example 1: Basic properties
    /// let x = bdd.mk_var(1);
    /// let f = bdd.mk_var(2);
    ///
    /// // f|1 = f
    /// assert_eq!(bdd.constrain(f, bdd.one()), f);
    ///
    /// // f|0 = 0
    /// assert_eq!(bdd.constrain(f, bdd.zero()), bdd.zero());
    ///
    /// // f|f = 1
    /// assert_eq!(bdd.constrain(x, x), bdd.one());
    ///
    /// // Example 2: Simplification
    /// // f = x1*x3 + ~x1*(x2^x3)
    /// // g = x1*x2 + ~x2*~x3
    /// // f|g = x1*x2*x3 (simplified form of f restricted to g's domain)
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let x3 = bdd.mk_var(3);
    ///
    /// let f = bdd.apply_or(
    ///     bdd.apply_and(x1, x3),
    ///     bdd.apply_and(-x1, bdd.apply_xor(x2, x3))
    /// );
    /// let g = bdd.apply_or(
    ///     bdd.apply_and(x1, x2),
    ///     bdd.apply_and(-x2, -x3)
    /// );
    ///
    /// let fg = bdd.constrain(f, g);
    /// let expected = bdd.mk_cube([1, 2, 3]); // x1*x2*x3
    /// assert_eq!(fg, expected);
    /// ```
    pub fn constrain(&self, f: Ref, g: Ref) -> Ref {
        debug!("constrain(f = {}, g = {})", f, g);

        if self.is_zero(g) {
            debug!("g is zero => f|g = 0");
            return self.zero();
        }
        if self.is_one(g) {
            debug!("g is one => f|g = f");
            return f;
        }
        if self.is_terminal(f) {
            debug!("f is terminal => f|g = f");
            return f;
        }
        if f == g {
            debug!("f = g => f|g = 1");
            return self.one();
        }
        if f == -g {
            debug!("f = ~g => f|g = 0");
            return self.zero();
        }

        let key = OpKey::Constrain(f, g);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: constrain(f = {}, g = {}) -> {}", f, g, res);
            return res;
        }

        // TODO: is it necessary to compute min var, or we can just use var(g)?
        let i = self.variable(f.id());
        let j = self.variable(g.id());
        let v = self.top_variable(i, j);
        debug!("top variable = {}", v);

        let (f0, f1) = self.top_cofactors(f, v);
        let (g0, g1) = self.top_cofactors(g, v);

        if self.is_zero(g1) {
            debug!("g1 is zero");
            return self.constrain(f0, g0);
        }
        if self.is_zero(g0) {
            debug!("g0 is zero");
            return self.constrain(f1, g1);
        }

        if f0 == f1 {
            debug!("f0 == f1");
            let low = self.constrain(f, g0);
            let high = self.constrain(f, g1);
            return self.mk_node(v, low, high);
        }

        let low = self.constrain(f0, g0);
        let high = self.constrain(f1, g1);
        // TODO: replace 'mk_node' with 'ITE'?
        let res = self.mk_node(v, low, high);
        debug!("computed: constrain(f = {}, g = {}) -> {}", f, g, res);

        self.cache_mut().insert(key, res);
        res
    }

    /// Restricts a BDD by setting variables where the constraint is constant.
    ///
    /// The restrict operator `f↓g` simplifies `f` by setting variables to constants
    /// based on `g`. Unlike [`constrain`](Bdd::constrain), restrict only substitutes
    /// variables that are constant in `g`, making it a partial evaluation.
    ///
    /// # Properties
    ///
    /// - `f↓1 = f`
    /// - `f↓0 = 0`
    /// - `f↓f = 1`
    /// - `f↓~f = 0`
    ///
    /// # Parameters
    ///
    /// * `f` - The function to restrict
    /// * `g` - The constraint defining variable assignments
    ///
    /// # Returns
    ///
    /// A BDD representing `f` restricted by `g`.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x OR y
    /// let f = bdd.apply_or(x, y);
    ///
    /// // Restrict f by setting x = true
    /// let result = bdd.restrict(f, x);
    /// assert_eq!(result, bdd.one()); // (true OR y) = true
    /// ```
    pub fn restrict(&self, f: Ref, g: Ref) -> Ref {
        debug!("restrict(f = {}, g = {})", f, g);

        if self.is_zero(g) {
            log::warn!("g is zero => f|g = 0");
            return self.zero();
        }
        if self.is_one(g) || self.is_terminal(f) {
            return f;
        }
        if f == g {
            return self.one();
        }
        if f == -g {
            return self.zero();
        }

        let key = OpKey::Restrict(f, g);
        if let Some(&res) = self.cache().get(&key) {
            debug!("cache: restrict(f = {}, g = {}) -> {}", f, g, res);
            return res;
        }

        let i = self.variable(f.id());
        let j = self.variable(g.id());
        let v = self.top_variable(i, j);

        let (f0, f1) = self.top_cofactors(f, v);
        let (g0, g1) = self.top_cofactors(g, v);

        if self.is_zero(g1) {
            return self.restrict(f0, g0);
        }
        if self.is_zero(g0) {
            return self.restrict(f1, g1);
        }

        let res = if v == i {
            let low = self.restrict(f0, g0);
            let high = self.restrict(f1, g1);
            self.mk_node(v, low, high)
        } else {
            self.restrict(f, self.apply_ite(g1, self.one(), g0))
        };
        self.cache_mut().insert(key, res);
        res
    }
}

// ============================================================================
// Variable renaming
// ============================================================================

impl Bdd {
    /// Renames variables according to an **order-preserving** permutation mapping.
    ///
    /// **IMPORTANT**: This function requires that the permutation preserves the variable
    /// ordering to maintain the OBDD invariant. If `old_var1 < old_var2` and both are
    /// in the permutation, then `new_var1 < new_var2` must hold.
    ///
    /// # Arguments
    ///
    /// * `f` - The BDD to rename variables in
    /// * `permutation` - HashMap mapping old variables to new ones.
    ///   Variables not in the map remain unchanged.
    ///
    /// # Panics
    ///
    /// Panics if the permutation is not order-preserving.
    ///
    /// # Returns
    ///
    /// A new BDD with variables renamed according to the permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    /// use std::collections::HashMap;
    ///
    /// let bdd = Bdd::default();
    /// // Pre-allocate all variables in order [1, 2, 3]
    /// let x1 = bdd.mk_var(1);
    /// let x2 = bdd.mk_var(2);
    /// let x3 = bdd.mk_var(3);
    ///
    /// // f = x1 ∧ ¬x2
    /// let f = bdd.apply_and(x1, -x2);
    ///
    /// // Order-preserving rename: x1→x2, x2→x3 (1<2 and 2<3, so order preserved)
    /// let mut perm = HashMap::new();
    /// perm.insert(Var::new(1), Var::new(2));
    /// perm.insert(Var::new(2), Var::new(3));
    /// let g = bdd.rename_vars(f, &perm);
    ///
    /// // Verify: g = x2 ∧ ¬x3
    /// let expected = bdd.apply_and(x2, -x3);
    /// assert_eq!(g, expected);
    /// ```
    pub fn rename_vars(&self, f: Ref, permutation: &HashMap<Var, Var>) -> Ref {
        // Validate that all variables in the permutation are registered in the ordering
        for (old_var, new_var) in permutation.iter() {
            assert!(
                self.get_level(*old_var).is_some(),
                "Old variable {} is not registered in the ordering. \
                All variables must be pre-allocated before rename.",
                old_var
            );
            assert!(
                self.get_level(*new_var).is_some(),
                "New variable {} is not registered in the ordering. \
                All variables must be pre-allocated before rename.",
                new_var
            );
        }

        // Validate that the permutation is order-preserving:
        // If old_i precedes old_j in the ordering, then new_i must precede new_j.
        //   (old_i < old_j) => (new_i < new_j)
        let mut sorted_pairs: Vec<_> = permutation.iter().collect();
        // Sort by level of the OLD variables
        sorted_pairs.sort_unstable_by(|&(old_a, _), &(old_b, _)| self.var_cmp(*old_a, *old_b));

        for i in 0..sorted_pairs.len() {
            for j in i + 1..sorted_pairs.len() {
                let (old_i, new_i) = sorted_pairs[i];
                let (old_j, new_j) = sorted_pairs[j];
                // old_i precedes old_j (by construction of sorted_pairs)
                // so new_i must also precede new_j for order preservation
                assert!(
                    self.var_precedes(*new_i, *new_j),
                    "Permutation is not order-preserving: {}→{} and {}→{} violates ordering invariant \
                    (new variable {} should precede {} in the ordering).",
                    old_i,
                    new_i,
                    old_j,
                    new_j,
                    new_i,
                    new_j
                );
            }
        }

        let mut cache = Cache::new(16);
        self.rename_vars_(f, permutation, &mut cache)
    }

    fn rename_vars_(&self, f: Ref, permutation: &HashMap<Var, Var>, cache: &mut Cache<Ref, Ref>) -> Ref {
        // Terminals pass through unchanged
        if self.is_terminal(f) {
            return f;
        }

        // Check cache (cache on the original reference including negation)
        if let Some(&result) = cache.get(&f) {
            return result;
        }

        // Handle negation: rename the positive node and negate the result
        let is_negated = f.is_negated();
        let f_positive = if is_negated { -f } else { f };

        // Get the variable and children
        let id = f_positive.id();
        let v = self.variable(id);
        let low = self.low(id);
        let high = self.high(id);

        // Recursively rename variables in children
        let low_new = self.rename_vars_(low, permutation, cache);
        let high_new = self.rename_vars_(high, permutation, cache);

        // Apply permutation to variable (or keep original if not in map)
        let v_new = permutation.get(&v).copied().unwrap_or(v);

        // Create new node with renamed variable
        let result_positive = self.mk_node(v_new, low_new, high_new);
        let result = if is_negated { -result_positive } else { result_positive };

        cache.insert(f, result);
        result
    }
}

// ============================================================================
// Quantification
// ============================================================================

impl Bdd {
    /// Performs existential quantification over a set of variables.
    ///
    /// Returns a new BDD where all occurrences of the specified variables are existentially
    /// quantified out. This is equivalent to the disjunction over all possible assignments
    /// to those variables:
    ///
    /// `∃x.f = f|x=0 ∨ f|x=1`
    ///
    /// For multiple variables:
    /// `∃{x₁,...,xₙ}.f = ⋁ f|x₁=b₁,...,xₙ=bₙ`
    ///
    /// This operation is fundamental for many symbolic algorithms, including:
    /// - Computing image/preimage in model checking
    /// - Relational product computation
    /// - Variable elimination in quantified Boolean formulas
    ///
    /// # Implementation
    ///
    /// This is a one-pass efficient implementation that performs quantification during
    /// a single recursive traversal, rather than computing two cofactors and ORing them.
    /// Variables are eliminated as soon as they are encountered in the BDD.
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to quantify
    /// * `vars` - Variables to existentially quantify out
    ///
    /// # Returns
    ///
    /// A BDD representing `∃vars.f`
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::Var;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x AND y
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Quantify out x: ∃x.(x ∧ y) = y (using raw integer)
    /// let result = bdd.exists(f, [1]);
    /// assert_eq!(result, y);
    ///
    /// // Quantify out both: ∃x,y.(x ∧ y) = true (using Var)
    /// let result = bdd.exists(f, [Var::new(1), Var::new(2)]);
    /// assert_eq!(result, bdd.one());
    /// ```
    ///
    /// # Performance
    ///
    /// The method uses internal caching to avoid recomputation. For best performance,
    /// the variable list should be sorted, though this is not required for correctness.
    pub fn exists(&self, f: Ref, vars: impl IntoIterator<Item = impl Into<Var>>) -> Ref {
        // Filter out variables not in the ordering and sort by level
        let mut vars_sorted: Vec<Var> = vars
            .into_iter()
            .map(|v| v.into())
            .filter(|&v| self.get_level(v).is_some())
            .collect();
        if vars_sorted.is_empty() {
            return f;
        }
        vars_sorted.sort_unstable_by(|a, b| self.var_cmp(*a, *b));
        let mut cache = Cache::new(16);
        self.exists_(f, &vars_sorted, 0, &mut cache)
    }

    fn exists_(&self, node: Ref, vars: &[Var], var_idx: usize, cache: &mut Cache<(Ref, usize), Ref>) -> Ref {
        debug!("exists(node = {}, vars = {:?}, var_idx = {})", node, vars, var_idx);

        if self.is_terminal(node) {
            return node;
        }

        // If we've exhausted all variables to quantify, return the node
        if var_idx >= vars.len() {
            return node;
        }

        let key = (node, var_idx);
        if let Some(&res) = cache.get(&key) {
            debug!("cache: exists({:?}) -> {}", key, res);
            return res;
        }

        let v = self.variable(node.id());
        let current_var = vars[var_idx];

        let res = if self.var_precedes(v, current_var) {
            // Node's variable precedes the current quantification variable in the ordering
            // Recurse on both children
            let low = self.low_node(node);
            let high = self.high_node(node);
            let r0 = self.exists_(low, vars, var_idx, cache);
            let r1 = self.exists_(high, vars, var_idx, cache);
            self.mk_node(v, r0, r1)
        } else if v == current_var {
            // Found the variable to quantify out
            // Compute f|v=0 ∨ f|v=1
            let low = self.low_node(node);
            let high = self.high_node(node);
            let r0 = self.exists_(low, vars, var_idx + 1, cache);
            let r1 = self.exists_(high, vars, var_idx + 1, cache);
            self.apply_or(r0, r1)
        } else {
            // current_var precedes v: the quantification variable doesn't appear in this subtree
            // Skip to the next quantification variable
            self.exists_(node, vars, var_idx + 1, cache)
        };

        cache.insert(key, res);
        debug!("computed: exists({:?}) -> {}", key, res);
        res
    }

    /// Performs universal quantification over a set of variables.
    ///
    /// Returns a new BDD where all occurrences of the specified variables are universally
    /// quantified out. This is equivalent to the conjunction over all possible assignments
    /// to those variables:
    ///
    /// `∀x.f = f|x=0 ∧ f|x=1`
    ///
    /// For multiple variables:
    /// `∀{x₁,...,xₙ}.f = ⋀ f|x₁=b₁,...,xₙ=bₙ`
    ///
    /// Universal quantification can be expressed in terms of existential quantification:
    /// `∀x.f = ¬∃x.¬f`
    ///
    /// # Parameters
    ///
    /// * `f` - The BDD to quantify
    /// * `vars` - Variables to universally quantify out
    ///
    /// # Returns
    ///
    /// A BDD representing `∀vars.f`
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // f = x OR y
    /// let f = bdd.apply_or(x, y);
    ///
    /// // Quantify out x: ∀x.(x ∨ y) = y
    /// let result = bdd.forall(f, [1]);
    /// assert_eq!(result, y);
    ///
    /// // Quantify out both: ∀x,y.(x ∨ y) = false
    /// let result = bdd.forall(f, [1, 2]);
    /// assert_eq!(result, bdd.zero());
    /// ```
    pub fn forall(&self, f: Ref, vars: impl IntoIterator<Item = impl Into<Var>>) -> Ref {
        let vars: Vec<Var> = vars.into_iter().map(|v| v.into()).collect();
        // ∀x.f = ¬∃x.¬f
        -self.exists(-f, vars)
    }

    /// Computes the relational product of two BDDs with existential quantification.
    ///
    /// The relational product combines conjunction and existential quantification in one
    /// efficient operation:
    ///
    /// `relProduct(u, v, vars) = ∃vars.(u ∧ v)`
    ///
    /// This is more efficient than computing `exists(apply_and(u, v), vars)` because
    /// quantification is performed during the conjunction operation, potentially producing
    /// a much smaller intermediate result.
    ///
    /// # Applications
    ///
    /// Relational product is fundamental in symbolic model checking and other applications:
    /// - **Image computation**: Computing successor states in state transition systems
    /// - **Reachability analysis**: Finding all reachable states
    /// - **Relational composition**: Composing two relations
    ///
    /// # Parameters
    ///
    /// * `u` - First BDD operand
    /// * `v` - Second BDD operand
    /// * `vars` - Variables to existentially quantify out
    ///
    /// # Returns
    ///
    /// A BDD representing `∃vars.(u ∧ v)`
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// // Relation 1: x implies y
    /// let r1 = bdd.apply_imply(x, y);
    /// // Relation 2: y implies z
    /// let r2 = bdd.apply_imply(y, z);
    ///
    /// // Compose relations by eliminating the intermediate variable y
    /// // Result: x implies z
    /// let composed = bdd.rel_product(r1, r2, [2]);
    /// let expected = bdd.apply_imply(x, z);
    /// assert_eq!(composed, expected);
    /// ```
    ///
    /// # Performance
    ///
    /// This operation is significantly more efficient than computing the AND first and
    /// then quantifying, especially when the intermediate result would be large.
    pub fn rel_product(&self, u: Ref, v: Ref, vars: impl IntoIterator<Item = impl Into<Var>>) -> Ref {
        // Filter out variables not in the ordering and sort by level
        let mut vars_sorted: Vec<Var> = vars
            .into_iter()
            .map(|x| x.into())
            .filter(|&v| self.get_level(v).is_some())
            .collect();
        if vars_sorted.is_empty() {
            return self.apply_and(u, v);
        }
        vars_sorted.sort_unstable_by(|a, b| self.var_cmp(*a, *b));
        let mut cache = Cache::new(16);
        self.rel_product_(u, v, &vars_sorted, 0, &mut cache)
    }

    fn rel_product_(&self, u: Ref, v: Ref, vars: &[Var], var_idx: usize, cache: &mut Cache<(Ref, Ref, usize), Ref>) -> Ref {
        debug!("rel_product(u = {}, v = {}, vars = {:?}, var_idx = {})", u, v, vars, var_idx);

        // Terminal cases
        if self.is_zero(u) || self.is_zero(v) {
            return self.zero();
        }
        if self.is_one(u) && self.is_one(v) {
            return self.one();
        }
        if self.is_one(u) {
            return self.exists_(v, vars, var_idx, &mut Cache::new(16));
        }
        if self.is_one(v) {
            return self.exists_(u, vars, var_idx, &mut Cache::new(16));
        }

        let key = (u, v, var_idx);
        if let Some(&res) = cache.get(&key) {
            debug!("cache: rel_product({:?}) -> {}", key, res);
            return res;
        }

        let i = self.variable(u.id());
        let j = self.variable(v.id());
        let m = self.top_variable(i, j);

        let (u0, u1) = self.top_cofactors(u, m);
        let (v0, v1) = self.top_cofactors(v, m);

        let res = if var_idx < vars.len() && m == vars[var_idx] {
            // This variable should be quantified out
            let h0 = self.rel_product_(u0, v0, vars, var_idx + 1, cache);
            let h1 = self.rel_product_(u1, v1, vars, var_idx + 1, cache);
            self.apply_or(h0, h1)
        } else {
            // Keep this variable
            let h0 = self.rel_product_(u0, v0, vars, var_idx, cache);
            let h1 = self.rel_product_(u1, v1, vars, var_idx, cache);
            self.mk_node(m, h0, h1)
        };

        cache.insert(key, res);
        debug!("computed: rel_product({:?}) -> {}", key, res);
        res
    }
}

// ============================================================================
// BDD analysis
// ============================================================================

impl Bdd {
    /// Returns all node indices reachable from the given BDD references.
    ///
    /// This performs a depth-first traversal from the root nodes to collect all reachable
    /// node indices. The terminal node (index 0) is always included in the result.
    ///
    /// # Arguments
    ///
    /// * `nodes` - An iterable collection of BDD references to start the traversal from
    ///
    /// # Returns
    ///
    /// A `HashSet<u32>` containing all unique node indices reachable from the given roots,
    /// including the terminal node (index 0).
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    /// use ananke_bdd::types::NodeId;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // Single variable: the variable node + terminal
    /// let desc = bdd.descendants([x]);
    /// assert_eq!(desc.len(), 2);
    /// assert!(desc.contains(&x.id()));
    /// assert!(desc.contains(&NodeId::TERMINAL)); // terminal
    ///
    /// // AND of two variables
    /// let f = bdd.apply_and(x, y);
    /// let desc = bdd.descendants([f]);
    /// assert!(desc.contains(&f.id()));
    /// assert!(desc.contains(&y.id()));
    /// assert!(desc.contains(&NodeId::TERMINAL)); // terminal
    /// ```
    ///
    /// # Multiple Roots
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let z = bdd.mk_var(3);
    ///
    /// let f1 = bdd.apply_and(x, y);
    /// let f2 = bdd.apply_and(y, z);
    ///
    /// // Descendants from multiple roots (shared nodes counted once)
    /// let desc = bdd.descendants([f1, f2]);
    /// assert!(desc.contains(&f1.id()));
    /// assert!(desc.contains(&f2.id()));
    /// assert!(desc.contains(&y.id())); // shared
    /// ```
    pub fn descendants(&self, nodes: impl IntoIterator<Item = Ref>) -> HashSet<NodeId> {
        let mut visited = HashSet::new();
        visited.insert(NodeId::TERMINAL);
        let mut stack = Vec::from_iter(nodes.into_iter().map(|node_ref| node_ref.id()));

        while let Some(i) = stack.pop() {
            if visited.insert(i) {
                let node = self.node(i);
                let low = node.low.id();
                if !low.is_terminal() {
                    stack.push(low);
                }
                let high = node.high.id();
                if !high.is_terminal() {
                    stack.push(high);
                }
            }
        }

        visited
    }

    /// Returns the number of nodes in a BDD.
    ///
    /// This counts all unique nodes reachable from the given node, including the terminal.
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // Single variable
    /// assert_eq!(bdd.size(x), 2);
    ///
    /// // AND of two variables
    /// let and = bdd.apply_and(x, y);
    /// assert_eq!(bdd.size(and), 3);
    ///
    /// // Tautology (just the terminal)
    /// assert_eq!(bdd.size(bdd.one()), 1);
    /// ```
    pub fn size(&self, node_ref: Ref) -> u64 {
        debug!("size(f = {})", node_ref);
        if let Some(&size) = self.size_cache().get(&node_ref) {
            debug!("cache: size({}) -> {}", node_ref, size);
            return size;
        }
        let size = self.descendants([node_ref]).len() as u64;
        debug!("computed: size({}) -> {}", node_ref, size);
        self.size_cache_mut().insert(node_ref, size);
        size
    }

    /// Count the total number of nodes in a set of BDDs.
    ///
    /// This efficiently counts the total number of unique nodes reachable
    /// from the given set of roots, avoiding double-counting shared nodes.
    /// This matches the behavior of `size()` - counting unique node indices
    /// including the terminal but not counting separate visits.
    ///
    /// # Arguments
    ///
    /// * `roots` - BDD roots to count nodes for
    ///
    /// # Returns
    ///
    /// The total number of unique nodes (including terminal)
    pub fn count_nodes(&self, roots: &[Ref]) -> usize {
        self.descendants(roots.iter().copied()).len()
    }

    /// Get the variables that appear in a set of BDDs (the *support*).
    ///
    /// # Arguments
    ///
    /// * `roots` - BDD roots to analyze
    ///
    /// # Returns
    ///
    /// A vector of variables that appear in the BDDs, sorted by their level in the ordering
    ///
    /// # Examples
    ///
    /// ```
    /// # use ananke_bdd::bdd::Bdd;
    /// # use ananke_bdd::types::Var;
    /// #
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    /// let f = bdd.apply_and(x, y);
    ///
    /// // Single BDD
    /// assert_eq!(bdd.support_variables(&[f]), vec![Var::new(1), Var::new(2)]);
    ///
    /// // Multiple BDDs
    /// let z = bdd.mk_var(3);
    /// assert_eq!(bdd.support_variables(&[x, z]), vec![Var::new(1), Var::new(3)]);
    /// ```
    pub fn support_variables(&self, roots: &[Ref]) -> Vec<Var> {
        let mut vars = HashSet::new();
        let mut visited = HashSet::new();
        visited.insert(NodeId::TERMINAL);

        let mut stack: Vec<_> = roots.iter().map(|r| r.id()).collect();

        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }

            let node = self.node(id);
            vars.insert(node.variable);

            let low_id = node.low.id();
            let high_id = node.high.id();
            if !low_id.is_terminal() {
                stack.push(low_id);
            }
            if !high_id.is_terminal() {
                stack.push(high_id);
            }
        }

        let mut result: Vec<Var> = vars.into_iter().collect();
        // Sort by level in the ordering
        result.sort_unstable_by(|a, b| self.var_cmp(*a, *b));
        result
    }

    /// Get the maximum variable (by level) that appears in the BDD.
    ///
    /// Returns `None` if the BDD is a terminal.
    ///
    /// Note: "maximum" refers to the variable closest to the terminals (highest level).
    pub fn max_variable(&self, root: Ref) -> Option<Var> {
        self.support_variables(&[root]).last().copied()
    }
}

// ============================================================================
// Garbage collection
// ============================================================================

impl Bdd {
    /// Performs garbage collection to reclaim unused BDD nodes.
    ///
    /// This removes all nodes that are not reachable from the provided roots.
    /// The operation also clears all caches. Only call this when you have identified
    /// all BDD nodes that should be kept.
    ///
    /// # Arguments
    ///
    /// * `roots` - Slice of BDD references that should be preserved
    ///
    /// # Examples
    ///
    /// ```
    /// use ananke_bdd::bdd::Bdd;
    ///
    /// let bdd = Bdd::default();
    /// let x = bdd.mk_var(1);
    /// let y = bdd.mk_var(2);
    ///
    /// // Create some temporary BDDs
    /// let _temp1 = bdd.apply_and(x, y);
    /// let _temp2 = bdd.apply_or(x, y);
    ///
    /// // Keep only the important result
    /// let important = bdd.apply_xor(x, y);
    ///
    /// // Collect garbage, keeping only 'important'
    /// bdd.collect_garbage(&[important]);
    /// // Nodes from temp1 and temp2 are now reclaimed
    /// ```
    pub fn collect_garbage(&self, roots: &[Ref]) {
        debug!("Collecting garbage...");

        self.cache_mut().clear();
        self.size_cache_mut().clear();

        let num_nodes = self.nodes().len();

        // Mark alive nodes using bit vector
        let alive = self.mark_alive(roots, num_nodes);

        // Collect dead node indices and remove from subtables
        let dead_indices: Vec<NodeId> = {
            let mut nodes = self.nodes_mut();
            let mut subtables = self.subtables_mut();
            let level_map = self.level_map();
            let free_set = self.free_set();

            (1..num_nodes)
                .filter_map(|idx| {
                    let id = NodeId::new(idx as u32);

                    // Skip if already free or alive
                    if free_set.contains(&id) || alive.contains(idx) {
                        return None;
                    }

                    // Dead node: remove from its subtable
                    let node = &nodes[idx];
                    let var = node.variable;
                    if !var.is_terminal() {
                        if let Some(&level) = level_map.get(&var) {
                            let low = node.low;
                            let high = node.high;
                            subtables[level.index()].remove(low, high, &mut nodes);
                        }
                    }
                    Some(id)
                })
                .collect()
        };

        // Add dead indices to free set for reuse
        self.free_set_mut().extend(dead_indices);

        debug!("Garbage collection complete");
    }

    /// Mark all nodes reachable from roots using a bit set.
    ///
    /// Returns a vector where `result[i]` is true if node `i` is alive.
    fn mark_alive(&self, roots: &[Ref], num_nodes: usize) -> BitSet {
        let mut alive = BitSet::new(num_nodes);
        alive.insert(0); // Terminal node is always alive

        let mut stack: Vec<NodeId> = roots.iter().map(|r| r.id()).collect();

        while let Some(id) = stack.pop() {
            if !alive.insert(id.index()) {
                // Already marked alive
                continue;
            }

            let node = self.node(id);
            let low_id = node.low.id();
            let high_id = node.high.id();

            if !alive.contains(low_id.index()) {
                stack.push(low_id);
            }
            if !alive.contains(high_id.index()) {
                stack.push(high_id);
            }
        }

        alive
    }
}

// ============================================================================
// String representation
// ============================================================================

impl Bdd {
    pub fn to_bracket_string(&self, node_ref: Ref) -> String {
        let mut visited = HashSet::new();
        self.node_to_str(node_ref, &mut visited)
    }

    fn node_to_str(&self, node_ref: Ref, visited: &mut HashSet<NodeId>) -> String {
        if self.is_zero(node_ref) {
            return "⊥".to_string();
        } else if self.is_one(node_ref) {
            return "⊤".to_string();
        }

        if !visited.insert(node_ref.id()) {
            return format!("{}", node_ref);
        }

        let id = node_ref.id();
        let Node { variable, low, high, .. } = self.node(id);

        format!(
            "{}:({}, {}, {})",
            node_ref,
            variable,
            self.node_to_str(high, visited),
            self.node_to_str(low, visited),
        )
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use super::*;

    #[test]
    fn test_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);

        assert_eq!(bdd.variable(x.id()), Var::new(1));
        assert_eq!(bdd.high_node(x), bdd.one());
        assert_eq!(bdd.low_node(x), bdd.zero());
    }

    #[test]
    fn test_not_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let not_x = -x;

        assert_eq!(bdd.variable(not_x.id()), Var::new(1));
        assert_eq!(bdd.high_node(not_x), bdd.zero());
        assert_eq!(bdd.low_node(not_x), bdd.one());
    }

    #[test]
    fn test_terminal() {
        let bdd = Bdd::default();

        assert_eq!(bdd.is_terminal(bdd.zero()), true);
        assert_eq!(bdd.is_zero(bdd.zero()), true);
        assert_eq!(bdd.is_one(bdd.zero()), false);

        assert_eq!(bdd.is_terminal(bdd.one()), true);
        assert_eq!(bdd.is_zero(bdd.one()), false);
        assert_eq!(bdd.is_one(bdd.one()), true);

        // Terminal node has variable 0 and invalid children (terminals have no children)
        assert_eq!(bdd.variable(bdd.zero().id()), Var::ZERO);
        assert_eq!(bdd.low(bdd.zero().id()).id(), NodeId::INVALID);
        assert_eq!(bdd.high(bdd.zero().id()).id(), NodeId::INVALID);

        assert_eq!(bdd.variable(bdd.one().id()), Var::ZERO);
        assert_eq!(bdd.low(bdd.one().id()).id(), NodeId::INVALID);
        assert_eq!(bdd.high(bdd.one().id()).id(), NodeId::INVALID);
    }

    #[test]
    fn test_cube() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3);
        let cube = bdd.mk_cube([1, 2, 3]);
        assert_eq!(f, cube);

        let f = bdd.apply_and(bdd.apply_and(x1, -x2), -x3);
        let cube = bdd.mk_cube([1, -2, -3]);
        assert_eq!(f, cube);
    }

    #[test]
    fn test_clause() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);
        let clause = bdd.mk_clause([1, 2, 3]);
        assert_eq!(f, clause);

        let f = bdd.apply_or(bdd.apply_or(x1, -x2), -x3);
        let clause = bdd.mk_clause([1, -2, -3]);
        assert_eq!(f, clause);
    }

    #[test]
    fn test_cube_with_preallocated_vars_different_order() {
        // This test ensures mk_cube correctly sorts by LEVEL, not by variable ID.
        // We pre-allocate variables in reverse order (3, 2, 1) so their levels are:
        //   var 3 -> level 0
        //   var 2 -> level 1
        //   var 1 -> level 2
        // Then we call mk_cube with variables in natural order (1, 2, 3),
        // forcing the implementation to sort by level.
        let bdd = Bdd::default();

        // Pre-allocate in reverse order
        let x3 = bdd.mk_var(3);
        let x2 = bdd.mk_var(2);
        let x1 = bdd.mk_var(1);

        // Build cube via apply_and: this respects the level ordering
        let expected = bdd.apply_and(bdd.apply_and(x1, x2), x3);

        // Call mk_cube with variables in natural order [1, 2, 3]
        // mk_cube must internally sort by level to get the same result
        let cube = bdd.mk_cube([1, 2, 3]);

        assert_eq!(expected, cube, "mk_cube should sort by level, not ID");
    }

    #[test]
    fn test_clause_with_preallocated_vars_different_order() {
        // This test ensures mk_clause correctly sorts by LEVEL, not by variable ID.
        // We pre-allocate variables in reverse order (3, 2, 1) so their levels are:
        //   var 3 -> level 0
        //   var 2 -> level 1
        //   var 1 -> level 2
        // Then we call mk_clause with variables in natural order (1, 2, 3),
        // forcing the implementation to sort by level.
        let bdd = Bdd::default();

        // Pre-allocate in reverse order
        let x3 = bdd.mk_var(3);
        let x2 = bdd.mk_var(2);
        let x1 = bdd.mk_var(1);

        // Build clause via apply_or: this respects the level ordering
        let expected = bdd.apply_or(bdd.apply_or(x1, x2), x3);

        // Call mk_clause with variables in natural order [1, 2, 3]
        // mk_clause must internally sort by level to get the same result
        let clause = bdd.mk_clause([1, 2, 3]);

        assert_eq!(expected, clause, "mk_clause should sort by level, not ID");
    }

    #[test]
    fn test_cube_with_arbitrary_allocation_order() {
        // Test with an even more complex allocation pattern: 2, 3, 1
        // Levels will be: var 2 -> 0, var 3 -> 1, var 1 -> 2
        let bdd = Bdd::default();

        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x1 = bdd.mk_var(1);

        // Build via apply_and
        let expected = bdd.apply_and(bdd.apply_and(x1, x2), x3);

        // Call mk_cube with literals in various orders
        let cube1 = bdd.mk_cube([1, 2, 3]);
        let cube2 = bdd.mk_cube([3, 1, 2]);
        let cube3 = bdd.mk_cube([2, 3, 1]);

        assert_eq!(expected, cube1);
        assert_eq!(expected, cube2);
        assert_eq!(expected, cube3);
    }

    #[test]
    fn test_clause_with_arbitrary_allocation_order() {
        // Test with an even more complex allocation pattern: 2, 3, 1
        // Levels will be: var 2 -> 0, var 3 -> 1, var 1 -> 2
        let bdd = Bdd::default();

        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x1 = bdd.mk_var(1);

        // Build via apply_or
        let expected = bdd.apply_or(bdd.apply_or(x1, x2), x3);

        // Call mk_clause with literals in various orders
        let clause1 = bdd.mk_clause([1, 2, 3]);
        let clause2 = bdd.mk_clause([3, 1, 2]);
        let clause3 = bdd.mk_clause([2, 3, 1]);

        assert_eq!(expected, clause1);
        assert_eq!(expected, clause2);
        assert_eq!(expected, clause3);
    }

    #[test]
    fn test_de_morgan_and() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = -bdd.apply_and(x, y);
        let g = bdd.apply_or(-x, -y);
        assert_eq!(f, g);
    }

    #[test]
    fn test_de_morgan_or() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);

        let f = -bdd.apply_or(x, y);
        let g = bdd.apply_and(-x, -y);
        assert_eq!(f, g);
    }

    #[test]
    fn test_xor_itself() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let res = bdd.apply_xor(f, f);
        assert_eq!(res, bdd.zero());
    }

    #[test]
    fn test_xor_contrary() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let f = bdd.apply_and(x, y);

        let res = bdd.apply_xor(f, -f);
        assert_eq!(res, bdd.one());
    }

    #[test]
    fn test_apply_ite() {
        let bdd = Bdd::default();

        // Terminal cases
        let g = bdd.mk_var(2);
        let h = bdd.mk_var(3);
        assert_eq!(bdd.apply_ite(bdd.one(), g, h), g);
        assert_eq!(bdd.apply_ite(bdd.zero(), g, h), h);

        // Functions
        let f = bdd.mk_node(Var::new(4), bdd.one(), h);
        assert_eq!(bdd.apply_ite(f, f, h), bdd.apply_or(f, h));
        assert_eq!(bdd.apply_ite(f, g, f), bdd.apply_and(f, g));
        assert_eq!(bdd.apply_ite(f, -g, bdd.one()), -bdd.apply_and(f, g));
        assert_eq!(bdd.apply_ite(f, bdd.zero(), -h), -bdd.apply_or(f, h));

        // Constants
        let f = bdd.mk_var(5);
        assert_eq!(bdd.apply_ite(f, g, g), g);
        assert_eq!(bdd.apply_ite(f, bdd.one(), bdd.zero()), f);
        assert_eq!(bdd.apply_ite(f, bdd.zero(), bdd.one()), -f);

        // General case
        let f = bdd.mk_var(6);
        let g = bdd.mk_var(7);
        let h = bdd.mk_var(8);
        let result = bdd.mk_node(bdd.variable(f.id()), -g, -h);
        assert_eq!(bdd.apply_ite(-f, -g, -h), result);
    }

    #[test]
    fn test_cofactor_cube() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2, 3]);
        println!("f = {}", bdd.to_bracket_string(f));

        assert_eq!(bdd.cofactor_cube(f, [1]), bdd.mk_cube([2, 3]));
        assert_eq!(bdd.cofactor_cube(f, [2]), bdd.mk_cube([1, 3]));
        assert_eq!(bdd.cofactor_cube(f, [3]), bdd.mk_cube([1, 2]));
        assert_eq!(bdd.cofactor_cube(f, [-1]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-2]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-3]), bdd.zero());

        assert_eq!(bdd.cofactor_cube(f, [1, 2]), bdd.mk_cube([3]));
        assert_eq!(bdd.cofactor_cube(f, [1, 3]), bdd.mk_cube([2]));
        assert_eq!(bdd.cofactor_cube(f, [2, 3]), bdd.mk_cube([1]));
        assert_eq!(bdd.cofactor_cube(f, [1, -2]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [1, -3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [2, -3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-1, 2]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-1, 3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-2, 3]), bdd.zero());

        assert_eq!(bdd.cofactor_cube(f, [1, 2, 3]), bdd.one());
        assert_eq!(bdd.cofactor_cube(f, [1, 2, -3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [1, -2, 3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [1, -2, -3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-1, 2, 3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-1, 2, -3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-1, -2, 3]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(f, [-1, -2, -3]), bdd.zero());

        assert_eq!(bdd.cofactor_cube(f, std::iter::empty::<i32>()), f);
        assert_eq!(bdd.cofactor_cube(bdd.one(), [1]), bdd.one());
        assert_eq!(bdd.cofactor_cube(bdd.zero(), [1]), bdd.zero());
        assert_eq!(bdd.cofactor_cube(bdd.one(), [-1]), bdd.one());
        assert_eq!(bdd.cofactor_cube(bdd.zero(), [-1]), bdd.zero());
    }

    impl Bdd {
        fn build_example(&self) -> Ref {
            let x1 = self.mk_var(1);
            let x2 = self.mk_var(2);
            let x3 = self.mk_var(3);

            // x1 ∨ (x2 ∧ x3)
            let f = self.apply_or(self.apply_and(x1, x2), x3);

            f
        }
    }

    #[test]
    fn test_constrain_base() {
        let bdd = Bdd::default();
        {
            let f = bdd.build_example();
            let g = bdd.one();
            let result = bdd.constrain(f, g);
            assert_eq!(result, f); // When g is 1, the result should be f.
        }
        {
            let f = bdd.build_example();
            let g = f;
            let result = bdd.constrain(f, g);
            assert_eq!(result, bdd.one()); // When g is f, the result should be 1.
        }
        {
            let f = bdd.zero();
            let g = bdd.build_example();
            let result = bdd.constrain(f, g);
            assert_eq!(result, bdd.zero()); // When f is 0, the result should be 0.
        }
    }

    // Somenzi, 1999
    #[test]
    fn test_constrain_example1() {
        let bdd = Bdd::default();

        // Pre-register variables in correct order (x1 at level 0, x2 at level 1, x3 at level 2)
        bdd.mk_var(1);
        bdd.mk_var(2);
        bdd.mk_var(3);

        let s = bdd.mk_node(Var::new(3), -bdd.one(), bdd.one());
        let p = bdd.mk_node(Var::new(2), -s, s);
        let r = bdd.mk_node(Var::new(2), s, bdd.one());
        let q = bdd.mk_node(Var::new(2), -s, bdd.one());
        let t = bdd.mk_node(Var::new(2), -bdd.one(), s);

        println!("s = {}", bdd.to_bracket_string(s));
        println!("p = {}", bdd.to_bracket_string(p));
        println!("r = {}", bdd.to_bracket_string(r));
        println!("q = {}", bdd.to_bracket_string(q));
        println!("t = {}", bdd.to_bracket_string(t));

        let f = bdd.mk_node(Var::new(1), -p, s);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.mk_node(Var::new(1), -r, q);
        println!("g = {}", bdd.to_bracket_string(g));
        let h = bdd.mk_node(Var::new(1), -bdd.one(), t);
        println!("h = {}", bdd.to_bracket_string(h));

        let fg = bdd.constrain(f, g);
        println!("f|g = {}", bdd.to_bracket_string(fg));

        assert_eq!(fg, h, "h = constrain(f, g)");
    }

    #[test]
    fn test_constrain_example2() {
        let bdd = Bdd::default();

        // f = x1*x3 + ~x1*(x2^x3)
        // g = x1*x2 + ~x2*~x3
        // h = f|g = x1*x2*x3
        // where:
        //   * is AND
        //   + is OR
        //   ^ is XOR
        //   ~ is NOT
        //   | is 'constrain'

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1*x3 + ~x1*(x2^x3)
        let f = bdd.apply_or(bdd.apply_and(x1, x3), bdd.apply_and(-x1, bdd.apply_xor(x2, x3)));

        // g = x1*x2 + ~x2*~x3
        let g = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(-x2, -x3));

        // h = x1*x2*x3
        let h = bdd.mk_cube([1, 2, 3]);

        // f|g == h
        let fg = bdd.constrain(f, g);
        assert_eq!(fg, h);
    }

    // Somenzi, 1999
    #[test]
    fn test_restrict() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let _y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        let s = bdd.mk_node(Var::new(3), -bdd.one(), bdd.one());
        let p = bdd.mk_node(Var::new(2), -s, s);
        let r = bdd.mk_node(Var::new(2), s, bdd.one());
        let q = bdd.mk_node(Var::new(2), -s, bdd.one());
        let t = bdd.mk_node(Var::new(2), -bdd.one(), s);

        println!("s = {}", bdd.to_bracket_string(s));
        println!("p = {}", bdd.to_bracket_string(p));
        println!("r = {}", bdd.to_bracket_string(r));
        println!("q = {}", bdd.to_bracket_string(q));
        println!("t = {}", bdd.to_bracket_string(t));

        let f = bdd.mk_node(Var::new(1), -p, s);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.mk_node(Var::new(1), -r, q);
        println!("g = {}", bdd.to_bracket_string(g));
        let h = bdd.apply_and(x, z);
        println!("h = {}", bdd.to_bracket_string(h));

        let fg = bdd.restrict(f, g);
        println!("f||g = {}", bdd.to_bracket_string(fg));
        assert_eq!(fg, h, "h = restrict(f, g)");
    }

    #[test]
    fn test_negation_in_ite_cache() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        println!("x1 = {}", bdd.to_bracket_string(x1));
        let x2 = bdd.mk_var(2);
        println!("x2 = {}", bdd.to_bracket_string(x2));

        let f = bdd.apply_xor(x1, x2);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.apply_xor(x1, x2);
        println!("g = {}", bdd.to_bracket_string(g));

        let f = bdd.apply_xor(x1, -x2);
        println!("f = {}", bdd.to_bracket_string(f));
        let g = bdd.apply_xor(x1, -x2);
        println!("g = {}", bdd.to_bracket_string(g));
        assert_eq!(f, g);
    }

    #[test]
    fn test_substitute() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = (x1 == x2) | x3
        let f = bdd.apply_or(bdd.apply_eq(x1, x2), x3);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        // f[x2<-0] = (x1 == 0) | x3 = ~x1 | x3
        let f_x2_zero = bdd.substitute(f, 2, false); // f|x2<-0
        println!("f|x2<-0 of size {} = {}", bdd.size(f_x2_zero), bdd.to_bracket_string(f_x2_zero));

        // g = ~x1 | x3
        let g = bdd.apply_or(-x1, x3);
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        assert_eq!(f_x2_zero, g);
    }

    #[test]
    fn test_substitute_multi() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x4 = bdd.mk_var(4);

        let values = HashMap::from([(Var::new(2), true), (Var::new(4), false)]);
        println!("values = {:?}", values);

        let f = bdd.apply_and_many([-x1, x2, x3, -x4]);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let g = bdd.substitute_multi(f, &values); // result of f|(x2<-1,x4<-0)
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        let h = bdd.apply_and(-x1, x3); // expected
        println!("h of size {} = {}", bdd.size(h), bdd.to_bracket_string(h));

        assert_eq!(g, h);
    }

    #[test]
    fn test_compose() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(bdd.apply_eq(x1, x2), x3);
        println!("f of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        let g = -bdd.apply_eq(x1, x2);
        println!("g of size {} = {}", bdd.size(g), bdd.to_bracket_string(g));

        let h = bdd.compose(f, bdd.variable(x3.id()).id(), g);
        println!("h of size {} = {}", bdd.size(h), bdd.to_bracket_string(h));
        assert!(bdd.is_zero(h));
    }

    #[test]
    fn test_ite_constant() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f = bdd.apply_and(x1, x2);
        println!("f = x1&x2 of size {} = {}", bdd.size(f), bdd.to_bracket_string(f));

        println!("is_implies(f, x1) = {}", bdd.is_implies(f, x1));
        println!("is_implies(f, x2) = {}", bdd.is_implies(f, x2));
        println!("is_implies(f, -x1) = {}", bdd.is_implies(f, -x1));
        println!("is_implies(f, -x2) = {}", bdd.is_implies(f, -x2));
        println!("is_implies(f, x1&x2 = {}", bdd.is_implies(f, bdd.apply_and(x1, x2)));
        println!("is_implies(f, x1|x2 = {}", bdd.is_implies(f, bdd.apply_or(x1, x2)));

        assert!(bdd.is_implies(f, x1));
        assert!(bdd.is_implies(f, x2));
        assert!(!bdd.is_implies(f, -x1));
        assert!(!bdd.is_implies(f, -x2));
        assert!(bdd.is_implies(f, bdd.apply_and(x1, x2)));
        assert!(bdd.is_implies(f, bdd.apply_or(x1, x2)));
        assert!(bdd.is_implies(x1, bdd.one()));
        assert!(bdd.is_implies(x2, bdd.one()));
        assert!(bdd.is_implies(bdd.zero(), x1));
        assert!(bdd.is_implies(bdd.zero(), x2));
        assert!(bdd.is_implies(x1, bdd.apply_or(x1, x2)));
        assert!(bdd.is_implies(x2, bdd.apply_or(x1, x2)));
    }

    #[test]
    fn test_descendants_terminal() {
        let bdd = Bdd::default();

        // Terminal zero (index 0) has no descendants except itself
        let desc = bdd.descendants([bdd.zero()]);
        println!("descendants of zero: {:?}", desc);
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&NodeId::TERMINAL));

        // Terminal one (index 0) has itself as descendant
        let desc = bdd.descendants([bdd.one()]);
        println!("descendants of one: {:?}", desc);
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&NodeId::TERMINAL));

        // Both terminals together
        let desc = bdd.descendants([bdd.zero(), bdd.one()]);
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&NodeId::TERMINAL));
    }

    #[test]
    fn test_descendants_single_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        // Variable node x1 points to: high=one (0), low=zero (negated 0)
        // So descendants should be: x.index() and 0 (terminal)
        let desc = bdd.descendants([x]);
        assert_eq!(desc.len(), 2);
        assert!(desc.contains(&x.id()));
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal
    }

    #[test]
    fn test_descendants_negated_var() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let not_x = -x;

        // Negated reference points to same node, so descendants are the same
        let desc = bdd.descendants([not_x]);
        assert_eq!(desc.len(), 2);
        assert!(desc.contains(&x.id()));
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal
    }

    #[test]
    fn test_descendants_and() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);

        // f = x1 AND x2 creates a structure:
        // f_node -> (low=negated 0, high=x2_node)
        // x2_node -> (low=negated 0, high=0)
        let desc = bdd.descendants([f]);

        // Should include: f's index, x2's index, and terminal (0)
        assert!(desc.contains(&f.id()));
        assert!(desc.contains(&x2.id()));
        assert!(desc.contains(&NodeId::TERMINAL));

        // Should be at least 3 nodes
        assert!(desc.len() >= 3);
    }

    #[test]
    fn test_descendants_or() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_or(x1, x2);

        let desc = bdd.descendants([f]);

        // Should include the root and all reachable nodes
        assert!(desc.contains(&f.id()));
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal
        assert!(desc.len() >= 2);
    }

    #[test]
    fn test_descendants_cube() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2, 3]);
        let desc = bdd.descendants([f]);
        println!("cube descendants: {:?}, len = {}", desc, desc.len());

        // Cube x1 AND x2 AND x3 creates a chain:
        // x1_node -> x2_node -> x3_node -> terminal
        assert!(desc.contains(&f.id()));
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal

        // Should have at least 4 nodes: 3 variable nodes + 1 terminal
        assert!(desc.len() >= 4, "desc.len() = {} < 4", desc.len());
    }

    #[test]
    fn test_descendants_multiple_roots() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f1 = bdd.apply_and(x1, x2);
        let f2 = bdd.apply_and(x2, x3);

        // Get descendants from both roots
        let desc = bdd.descendants([f1, f2]);

        // Should include nodes from both formulas
        assert!(desc.contains(&f1.id()));
        assert!(desc.contains(&f2.id()));
        assert!(desc.contains(&x2.id())); // shared node
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal
    }

    #[test]
    fn test_descendants_shared_structure() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f1 = bdd.apply_and(x1, x2);
        let f2 = bdd.apply_or(x1, x2);

        // Both formulas share x1 and x2 nodes
        let desc1 = bdd.descendants([f1]);
        let desc2 = bdd.descendants([f2]);
        let desc_both = bdd.descendants([f1, f2]);

        // Union should not double-count shared nodes
        let union_size = desc1.union(&desc2).count();
        assert_eq!(desc_both.len(), union_size);
    }

    #[test]
    fn test_descendants_empty() {
        let bdd = Bdd::default();

        // Empty iterator should return just the terminal 0 (added by default)
        let desc = bdd.descendants(std::iter::empty());
        assert_eq!(desc.len(), 1);
        assert!(desc.contains(&NodeId::TERMINAL));
    }

    #[test]
    fn test_descendants_complex_formula() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // (x1 XOR x2) AND x3
        let xor = bdd.apply_xor(x1, x2);
        let f = bdd.apply_and(xor, x3);

        let desc = bdd.descendants([f]);

        // Should include all nodes in the formula
        assert!(desc.contains(&f.id()));
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal

        // XOR creates a larger structure
        assert!(desc.len() >= 4);
    }

    #[test]
    fn test_descendants_size_consistency() {
        let bdd = Bdd::default();

        let f = bdd.mk_cube([1, 2, 3]);

        // descendants should return the same count as size
        let desc = bdd.descendants([f]);
        let size = bdd.size(f);

        assert_eq!(desc.len() as u64, size);
    }

    #[test]
    fn test_descendants_negated_edges() {
        let bdd = Bdd::default();

        // Create a formula with negations
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(-x1, -x2);

        let desc = bdd.descendants([f]);

        // Negated edges don't create new nodes, just traverse to existing ones
        assert!(desc.contains(&f.id()));
        assert!(desc.contains(&NodeId::TERMINAL)); // terminal
    }

    #[test]
    fn test_to_bracket_string_terminal() {
        let bdd = Bdd::default();

        println!("zero = {}", bdd.to_bracket_string(bdd.zero()));
        assert_eq!(bdd.to_bracket_string(bdd.zero()), "⊥");

        println!("one = {}", bdd.to_bracket_string(bdd.one()));
        assert_eq!(bdd.to_bracket_string(bdd.one()), "⊤");
    }

    #[test]
    fn test_to_bracket_string_1() {
        let bdd = Bdd::default();

        // x1 ∧ x2
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));
        assert_eq!(bdd.to_bracket_string(f), "@3:(x1, @2:(x2, ⊤, ⊥), ⊥)");
    }

    #[test]
    fn test_to_bracket_string_2() {
        let bdd = Bdd::default();

        // ~x1 ∨ (~x2 ∧ x3)
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_or(-x1, bdd.apply_and(-x2, x3));
        println!("f = ~x1 ∨ (~x2 ∧ x3) = {}", bdd.to_bracket_string(f));
        assert_eq!(bdd.to_bracket_string(f), "~@5:(x1, @4:(x2, ⊤, ~@3:(x3, ⊤, ⊥)), ⊥)");
    }

    #[test]
    fn test_exists_single() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∧ x2
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));

        // ∃x1.(x1 ∧ x2) = x2
        let result = bdd.exists(f, [1]);
        println!("∃x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∃x2.(x1 ∧ x2) = x1
        let result = bdd.exists(f, [2]);
        println!("∃x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x1);
    }

    #[test]
    fn test_exists_multiple() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∧ x2 ∧ x3
        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3);
        println!("f = x1 ∧ x2 ∧ x3 = {}", bdd.to_bracket_string(f));

        // ∃x1,x3.(x1 ∧ x2 ∧ x3) = x2
        let result = bdd.exists(f, [1, 3]);
        println!("∃x1,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∃x1,x2,x3.(x1 ∧ x2 ∧ x3) = 1
        let result = bdd.exists(f, [1, 2, 3]);
        println!("∃x1,x2,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one());
    }

    #[test]
    fn test_exists_or() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∨ x2
        let f = bdd.apply_or(x1, x2);
        println!("f = x1 ∨ x2 = {}", bdd.to_bracket_string(f));

        // ∃x1.(x1 ∨ x2) = 1
        let result = bdd.exists(f, [1]);
        println!("∃x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one());

        // ∃x2.(x1 ∨ x2) = 1
        let result = bdd.exists(f, [2]);
        println!("∃x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one());
    }

    #[test]
    fn test_exists_complex() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = (x1 ∧ x2) ∨ (¬x1 ∧ x3)
        let c1 = bdd.apply_and(x1, x2);
        let c2 = bdd.apply_and(-x1, x3);
        let f = bdd.apply_or(c1, c2);
        println!("f = (x1 ∧ x2) ∨ (¬x1 ∧ x3) = {}", bdd.to_bracket_string(f));

        // ∃x1.f = x2 ∨ x3
        let result = bdd.exists(f, [1]);
        let expected = bdd.apply_or(x2, x3);
        println!("∃x1.f = {}", bdd.to_bracket_string(result));
        println!("expected = {}", bdd.to_bracket_string(expected));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_exists_empty_vars() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(x1, x2);

        // Quantifying no variables should return the same formula
        let result = bdd.exists(f, std::iter::empty::<Var>());
        assert_eq!(result, f);
    }

    #[test]
    fn test_exists_independent_vars() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∧ x2 (doesn't depend on x3, x4, x5)
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));

        // Quantify out x3 (which doesn't appear): should return the same formula
        let result = bdd.exists(f, [3]);
        println!("∃x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, f, "Quantifying independent variable should return same BDD");

        // Quantify out x3, x4, x5 (none appear): should return the same formula
        let result = bdd.exists(f, [3, 4, 5]);
        println!("∃x3,x4,x5.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, f, "Quantifying multiple independent variables should return same BDD");

        // Mix of dependent and independent variables
        // Quantify out x1, x3: ∃x1,x3.(x1 ∧ x2) = x2
        let result = bdd.exists(f, [1, 3]);
        println!("∃x1,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2, "Should correctly handle mix of dependent and independent variables");

        // Independent variables before dependent ones
        // Quantify out x3, x1, x5, x2 (x3,x5 don't appear)
        let result = bdd.exists(f, [3, 1, 5, 2]);
        println!("∃x3,x1,x5,x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.one(), "Should handle unsorted mix correctly");
    }

    #[test]
    fn test_forall_single() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∨ x2
        let f = bdd.apply_or(x1, x2);
        println!("f = x1 ∨ x2 = {}", bdd.to_bracket_string(f));

        // ∀x1.(x1 ∨ x2) = x2
        let result = bdd.forall(f, [1]);
        println!("∀x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∀x2.(x1 ∨ x2) = x1
        let result = bdd.forall(f, [2]);
        println!("∀x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x1);
    }

    #[test]
    fn test_forall_multiple() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∨ x2 ∨ x3
        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);
        println!("f = x1 ∨ x2 ∨ x3 = {}", bdd.to_bracket_string(f));

        // ∀x1,x3.(x1 ∨ x2 ∨ x3) = x2
        let result = bdd.forall(f, [1, 3]);
        println!("∀x1,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, x2);

        // ∀x1,x2,x3.(x1 ∨ x2 ∨ x3) = 0
        let result = bdd.forall(f, [1, 2, 3]);
        println!("∀x1,x2,x3.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.zero());
    }

    #[test]
    fn test_forall_and() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        // f = x1 ∧ x2
        let f = bdd.apply_and(x1, x2);
        println!("f = x1 ∧ x2 = {}", bdd.to_bracket_string(f));

        // ∀x1.(x1 ∧ x2) = 0
        let result = bdd.forall(f, [1]);
        println!("∀x1.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.zero());

        // ∀x2.(x1 ∧ x2) = 0
        let result = bdd.forall(f, [2]);
        println!("∀x2.f = {}", bdd.to_bracket_string(result));
        assert_eq!(result, bdd.zero());
    }

    #[test]
    fn test_rel_product_simple() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        // r1: x → y  (x implies y)
        let r1 = bdd.apply_imply(x, y);
        println!("r1 = x → y = {}", bdd.to_bracket_string(r1));

        // r2: y → z  (y implies z)
        let r2 = bdd.apply_imply(y, z);
        println!("r2 = y → z = {}", bdd.to_bracket_string(r2));

        // Compose: eliminate y to get x → z
        let result = bdd.rel_product(r1, r2, [2]);
        println!("∃y.(r1 ∧ r2) = {}", bdd.to_bracket_string(result));

        let expected = bdd.apply_imply(x, z);
        println!("expected = x → z = {}", bdd.to_bracket_string(expected));
        assert_eq!(result, expected);
    }

    #[test]
    fn test_rel_product_vs_exists() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        let f = bdd.apply_and(x1, x2);
        let g = bdd.apply_or(x2, x3);

        // Using rel_product
        let result1 = bdd.rel_product(f, g, [2]);
        println!("rel_product(f, g, [2]) = {}", bdd.to_bracket_string(result1));

        // Using exists(and(...))
        let result2 = bdd.exists(bdd.apply_and(f, g), [2]);
        println!("exists(f ∧ g, [2]) = {}", bdd.to_bracket_string(result2));

        // They should be equal
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_rel_product_empty_vars() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);

        let f = bdd.apply_and(x1, x2);
        let g = bdd.mk_var(3);

        // Relational product with no variables to eliminate is just AND
        let result = bdd.rel_product(f, g, std::iter::empty::<Var>());
        let expected = bdd.apply_and(f, g);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_rel_product_terminals() {
        let bdd = Bdd::default();

        let x = bdd.mk_var(1);

        // rel_product with zero should be zero
        let result = bdd.rel_product(bdd.zero(), x, [1]);
        assert_eq!(result, bdd.zero());

        let result = bdd.rel_product(x, bdd.zero(), [1]);
        assert_eq!(result, bdd.zero());

        // rel_product(1, 1, []) = 1
        let result = bdd.rel_product(bdd.one(), bdd.one(), std::iter::empty::<Var>());
        assert_eq!(result, bdd.one());
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_not_order_preserving() {
        let bdd = Bdd::default();

        // Pre-allocate both variables
        let x1 = bdd.mk_var(1);
        let _x2 = bdd.mk_var(2);

        // Rename x1→x2, x2→x1 (swap) - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(1));

        // This should panic
        let _result = bdd.rename_vars(x1, &perm);
    }

    #[test]
    fn test_rename_vars_chain() {
        let bdd = Bdd::default();

        // Pre-allocate all variables so ordering is [1, 2, 3]
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∧ ¬x2
        let f = bdd.apply_and(x1, -x2);

        // Chain rename: x1→x2, x2→x3
        // This is order-preserving: 1<2 maps to 2<3
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(3));

        let g = bdd.rename_vars(f, &perm); // g = x2 ∧ ¬x3

        // Create expected: x2 ∧ ¬x3
        let expected = bdd.apply_and(x2, -x3);

        assert_eq!(g, expected);
    }

    #[test]
    fn test_rename_vars_backward() {
        let bdd = Bdd::default();

        // Pre-allocate variables in natural order so the ordering is [1, 2, 3]
        let _x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_and(x2, x3); // f(x2, x3) = x2 ∧ x3

        // Current ordering: [1, 2, 3]
        // f uses only x2 (level 1) and x3 (level 2)

        // Backward rename: x2→x1, x3→x2
        // This is order-preserving: x2 < x3 in ordering, and x1 < x2 in ordering
        let mut perm = HashMap::new();
        perm.insert(Var::new(2), Var::new(1));
        perm.insert(Var::new(3), Var::new(2));

        let g = bdd.rename_vars(f, &perm); // g(x1, x2) = x1 ∧ x2

        // Verify it computes x1 ∧ x2 by checking all truth table entries
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-1, -2]))); // g[0,0] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-1, 2]))); // g[0,1] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [1, -2]))); // g[1,0] = 0
        assert!(bdd.is_one(bdd.cofactor_cube(g, [1, 2]))); // g[1,1] = 1
    }

    #[test]
    fn test_rename_vars_shift() {
        let bdd = Bdd::default();

        // Pre-allocate all variables in order [1, 2, 3, 4]
        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let _x3 = bdd.mk_var(3);
        let _x4 = bdd.mk_var(4);
        let f = bdd.apply_and(x1, x2); // f(x1, x2) = x1 ∧ x2

        // Shift: x1→x3, x2→x4 (order-preserving: 1<2 maps to 3<4)
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(3));
        perm.insert(Var::new(2), Var::new(4));

        let g = bdd.rename_vars(f, &perm); // g(x3, x4) = x3 ∧ x4

        // Verify it computes x3 ∧ x4 by checking all truth table entries
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-3, -4]))); // g[0,0] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [-3, 4]))); // g[0,1] = 0
        assert!(bdd.is_zero(bdd.cofactor_cube(g, [3, -4]))); // g[1,0] = 0
        assert!(bdd.is_one(bdd.cofactor_cube(g, [3, 4]))); // g[1,1] = 1
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_partial() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let f = bdd.apply_and(bdd.apply_and(x1, x2), x3); // x1 ∧ x2 ∧ x3

        // Only rename x1→x2, x2→x1 (swap), leave x3 unchanged - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(1));

        // This should panic
        let _g = bdd.rename_vars(f, &perm);
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_negation() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let f = bdd.apply_and(-x1, x2); // ¬x1 ∧ x2

        // Swap x1↔x2 - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(1));

        // This should panic
        let _g = bdd.rename_vars(f, &perm);
    }

    #[test]
    #[should_panic(expected = "Permutation is not order-preserving")]
    fn test_rename_vars_cyclic() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);

        // f = x1 ∨ x2 ∨ x3
        let f = bdd.apply_or(bdd.apply_or(x1, x2), x3);

        // Cyclic rename: x1→x2, x2→x3, x3→x1 (a cycle!) - NOT order-preserving!
        let mut perm = HashMap::new();
        perm.insert(Var::new(1), Var::new(2));
        perm.insert(Var::new(2), Var::new(3));
        perm.insert(Var::new(3), Var::new(1));

        // This should panic
        let _g = bdd.rename_vars(f, &perm);
    }

    // ========================================================================
    // Variable ordering API tests
    // ========================================================================

    #[test]
    fn test_set_variable_order_basic() {
        let bdd = Bdd::default();

        // Set custom order: y < x < z (by level)
        bdd.set_variable_order([2u32, 1, 3]);

        // Create variables - they should be at the defined levels
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let _z = bdd.mk_var(3);

        // Check ordering
        let order = bdd.get_variable_order();
        assert_eq!(order, vec![Var::new(2), Var::new(1), Var::new(3)]);

        // Check levels
        assert_eq!(bdd.get_level(Var::new(2)).unwrap().index(), 0); // y at level 0
        assert_eq!(bdd.get_level(Var::new(1)).unwrap().index(), 1); // x at level 1
        assert_eq!(bdd.get_level(Var::new(3)).unwrap().index(), 2); // z at level 2

        // Verify y is the root variable in y ∧ x
        let f = bdd.apply_and(y, x);
        assert_eq!(bdd.variable(f.id()), Var::new(2)); // y is root
    }

    #[test]
    fn test_set_variable_order_preserves_function() {
        let bdd = Bdd::default();

        // Custom order: 3 < 1 < 2
        bdd.set_variable_order([3u32, 1, 2]);

        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);

        // f = x ∧ (y ∨ z)
        let f = bdd.apply_and(x, bdd.apply_or(y, z));

        // Verify the function computes correctly
        assert!(bdd.is_one(bdd.cofactor_cube(f, [1, 2, 3]))); // x=1, y=1, z=1
        assert!(bdd.is_one(bdd.cofactor_cube(f, [1, 2, -3]))); // x=1, y=1, z=0
        assert!(bdd.is_one(bdd.cofactor_cube(f, [1, -2, 3]))); // x=1, y=0, z=1
        assert!(bdd.is_zero(bdd.cofactor_cube(f, [1, -2, -3]))); // x=1, y=0, z=0
        assert!(bdd.is_zero(bdd.cofactor_cube(f, [-1, 2, 3]))); // x=0, y=1, z=1
    }

    #[test]
    #[should_panic(expected = "set_variable_order must be called before creating any BDD nodes")]
    fn test_set_variable_order_after_nodes_panics() {
        let bdd = Bdd::default();

        // Create a BDD node first
        let _x = bdd.mk_var(1);

        // This should panic - order must be set before nodes are created
        bdd.set_variable_order([2u32, 1, 3]);
    }

    #[test]
    #[should_panic(expected = "Variable order has already been set")]
    fn test_set_variable_order_twice_panics() {
        let bdd = Bdd::default();

        bdd.set_variable_order([1u32, 2, 3]);

        // This should panic - order already set
        bdd.set_variable_order([3u32, 2, 1]);
    }

    #[test]
    #[should_panic(expected = "Duplicate variable")]
    fn test_set_variable_order_duplicates_panics() {
        let bdd = Bdd::default();

        // This should panic - duplicate variable 1
        bdd.set_variable_order([1u32, 2, 1]);
    }

    #[test]
    fn test_apply_variable_order_basic() {
        let bdd = Bdd::default();

        // Create BDD with default order 1, 2, 3
        let x = bdd.mk_var(1);
        let y = bdd.mk_var(2);
        let z = bdd.mk_var(3);
        let f = bdd.apply_and(x, bdd.apply_or(y, z));

        assert_eq!(bdd.get_variable_order(), vec![Var::new(1), Var::new(2), Var::new(3)]);

        // Apply new order: 3, 1, 2
        let mut roots = vec![f];
        let stats = bdd.apply_variable_order(&mut roots, [3u32, 1, 2]);

        // Check new order
        assert_eq!(bdd.get_variable_order(), vec![Var::new(3), Var::new(1), Var::new(2)]);

        // Verify function is preserved
        let f_new = roots[0];
        assert!(bdd.is_one(bdd.cofactor_cube(f_new, [1, 2, 3]))); // x=1, y=1, z=1
        assert!(bdd.is_one(bdd.cofactor_cube(f_new, [1, 2, -3]))); // x=1, y=1, z=0
        assert!(bdd.is_one(bdd.cofactor_cube(f_new, [1, -2, 3]))); // x=1, y=0, z=1
        assert!(bdd.is_zero(bdd.cofactor_cube(f_new, [1, -2, -3]))); // x=1, y=0, z=0
        assert!(bdd.is_zero(bdd.cofactor_cube(f_new, [-1, 2, 3]))); // x=0, y=1, z=1

        // Check stats
        assert!(stats.swaps > 0);
    }

    #[test]
    fn test_apply_variable_order_reverse() {
        let bdd = Bdd::default();

        let x1 = bdd.mk_var(1);
        let x2 = bdd.mk_var(2);
        let x3 = bdd.mk_var(3);
        let x4 = bdd.mk_var(4);

        // f = (x1 ∧ x2) ∨ (x3 ∧ x4)
        let f = bdd.apply_or(bdd.apply_and(x1, x2), bdd.apply_and(x3, x4));

        let original_size = bdd.size(f);

        // Reverse the order
        let mut roots = vec![f];
        bdd.apply_variable_order(&mut roots, [4u32, 3, 2, 1]);

        assert_eq!(bdd.get_variable_order(), vec![Var::new(4), Var::new(3), Var::new(2), Var::new(1)]);

        // Function should still compute the same thing
        let f_new = roots[0];
        assert!(bdd.is_one(bdd.cofactor_cube(f_new, [1, 2, -3, -4]))); // x1∧x2
        assert!(bdd.is_one(bdd.cofactor_cube(f_new, [-1, -2, 3, 4]))); // x3∧x4
        assert!(bdd.is_zero(bdd.cofactor_cube(f_new, [-1, -2, -3, -4]))); // all false

        // Size might change due to different ordering
        let new_size = bdd.size(f_new);
        println!("Size before: {}, after reverse: {}", original_size, new_size);
    }
}
