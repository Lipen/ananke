//! The Canonical Interaction Graph (CIG) data structure.
//!
//! CIG is a DAG representation of Boolean functions based on their
//! interaction structure. Each node represents either a variable (leaf)
//! or a composition of child nodes via an interaction function.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHasher};

use crate::interaction::InteractionFunction;
use crate::partition::Partition;
use crate::variable::{Var, VarSet};

/// A node in the Canonical Interaction Graph.
#[derive(Clone, PartialEq, Eq)]
pub struct CigNode {
    /// The kind of node (leaf, internal, or constant).
    pub kind: CigNodeKind,
    /// Cached canonical hash for quick comparison.
    hash: u64,
}

/// The different kinds of CIG nodes.
#[derive(Clone, PartialEq, Eq)]
pub enum CigNodeKind {
    /// A constant (terminal) node.
    Constant(bool),
    /// A leaf node representing a single variable.
    Leaf(Var),
    /// An internal node with an interaction function and children.
    Internal {
        /// The interaction function combining children.
        interaction: InteractionFunction,
        /// Child nodes (canonically ordered).
        children: Vec<Arc<CigNode>>,
    },
}

impl CigNode {
    /// Create a constant node.
    pub fn constant(value: bool) -> Self {
        let hash = if value { 1 } else { 0 };
        CigNode {
            kind: CigNodeKind::Constant(value),
            hash,
        }
    }

    /// Create a leaf node for a variable.
    pub fn leaf(var: Var) -> Self {
        let hash = var.index() as u64 + 2; // Offset to avoid collision with constants
        CigNode {
            kind: CigNodeKind::Leaf(var),
            hash,
        }
    }

    /// Create an internal node.
    pub fn internal(interaction: InteractionFunction, children: Vec<Arc<CigNode>>) -> Self {
        // Compute hash from interaction and children
        let mut hasher = FxHasher::default();
        interaction.hash(&mut hasher);
        for child in children.iter() {
            hasher.write_u64(child.canonical_hash());
        }
        let hash = hasher.finish();

        CigNode {
            kind: CigNodeKind::Internal { interaction, children },
            hash,
        }
    }

    /// Get the canonical hash of this node.
    pub fn canonical_hash(&self) -> u64 {
        self.hash
    }

    /// Check if this is a constant node.
    pub fn is_constant(&self) -> bool {
        matches!(self.kind, CigNodeKind::Constant(_))
    }

    /// Check if this is a leaf node.
    pub fn is_leaf(&self) -> bool {
        matches!(self.kind, CigNodeKind::Leaf(_))
    }

    /// Check if this is an internal node.
    pub fn is_internal(&self) -> bool {
        matches!(self.kind, CigNodeKind::Internal { .. })
    }

    /// Get the constant value if this is a constant node.
    pub fn as_constant(&self) -> Option<bool> {
        match &self.kind {
            CigNodeKind::Constant(v) => Some(*v),
            _ => None,
        }
    }

    /// Get the variable if this is a leaf node.
    pub fn as_leaf(&self) -> Option<Var> {
        match &self.kind {
            CigNodeKind::Leaf(v) => Some(*v),
            _ => None,
        }
    }

    /// Get the interaction and children if this is an internal node.
    pub fn as_internal(&self) -> Option<(&InteractionFunction, &[Arc<CigNode>])> {
        match &self.kind {
            CigNodeKind::Internal { interaction, children } => Some((interaction, children)),
            _ => None,
        }
    }

    /// Get the number of children (0 for leaves/constants).
    pub fn num_children(&self) -> usize {
        match &self.kind {
            CigNodeKind::Constant(_) | CigNodeKind::Leaf(_) => 0,
            CigNodeKind::Internal { children, .. } => children.len(),
        }
    }

    /// Count all nodes in the subgraph rooted at this node.
    pub fn size(&self) -> usize {
        let mut visited = std::collections::HashSet::new();
        self.size_recursive(&mut visited)
    }

    fn size_recursive(&self, visited: &mut std::collections::HashSet<u64>) -> usize {
        if !visited.insert(self.hash) {
            return 0; // Already counted
        }

        match &self.kind {
            CigNodeKind::Constant(_) | CigNodeKind::Leaf(_) => 1,
            CigNodeKind::Internal { children, .. } => 1 + children.iter().map(|c| c.size_recursive(visited)).sum::<usize>(),
        }
    }

    /// Compute the depth of this node.
    pub fn depth(&self) -> usize {
        match &self.kind {
            CigNodeKind::Constant(_) | CigNodeKind::Leaf(_) => 0,
            CigNodeKind::Internal { children, .. } => 1 + children.iter().map(|c| c.depth()).max().unwrap_or(0),
        }
    }

    /// Get all variables in the subgraph.
    pub fn variables(&self) -> Vec<Var> {
        let mut vars = Vec::new();
        self.collect_variables(&mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_variables(&self, vars: &mut Vec<Var>) {
        match &self.kind {
            CigNodeKind::Constant(_) => {}
            CigNodeKind::Leaf(v) => vars.push(*v),
            CigNodeKind::Internal { children, .. } => {
                for child in children {
                    child.collect_variables(vars);
                }
            }
        }
    }

    /// Compute the interaction width (max arity of internal nodes).
    pub fn interaction_width(&self) -> usize {
        match &self.kind {
            CigNodeKind::Constant(_) | CigNodeKind::Leaf(_) => 0,
            CigNodeKind::Internal { interaction, children } => {
                let child_max = children.iter().map(|c| c.interaction_width()).max().unwrap_or(0);
                interaction.arity().max(child_max as u32) as usize
            }
        }
    }

    /// Compute the total interaction table size.
    pub fn table_size(&self) -> usize {
        match &self.kind {
            CigNodeKind::Constant(_) | CigNodeKind::Leaf(_) => 0,
            CigNodeKind::Internal { interaction, children } => interaction.size() + children.iter().map(|c| c.table_size()).sum::<usize>(),
        }
    }

    /// Extract the partition of variables represented by this CIG node.
    ///
    /// Returns a Partition where the blocks represent the grouping of variables
    /// at the top level of this node. If this is an internal node, each child's
    /// variables form a block.
    pub fn extract_partition(&self) -> Partition {
        match &self.kind {
            CigNodeKind::Constant(_) => Partition::from_blocks(vec![]),
            CigNodeKind::Leaf(v) => Partition::indiscrete(VarSet::singleton(*v)),
            CigNodeKind::Internal { children, .. } => {
                let blocks: Vec<VarSet> = children
                    .iter()
                    .map(|child| {
                        let vars = child.variables();
                        VarSet::from_iter(vars)
                    })
                    .collect();
                Partition::from_blocks(blocks)
            }
        }
    }
}

impl fmt::Debug for CigNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            CigNodeKind::Constant(v) => write!(f, "{}", if *v { "⊤" } else { "⊥" }),
            CigNodeKind::Leaf(v) => write!(f, "{}", v),
            CigNodeKind::Internal { interaction, children } => {
                write!(f, "{}(", interaction)?;
                for (i, child) in children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", child)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for CigNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.display_tree(f, "", true, true)
    }
}

impl CigNode {
    /// Display the node as a tree structure.
    fn display_tree(&self, f: &mut fmt::Formatter<'_>, prefix: &str, is_last: bool, is_root: bool) -> fmt::Result {
        // Determine connector for this node
        let connector = if is_root {
            ""
        } else if is_last {
            "└─ "
        } else {
            "├─ "
        };

        match &self.kind {
            CigNodeKind::Constant(v) => {
                writeln!(f, "{}{}{}", prefix, connector, if *v { "⊤" } else { "⊥" })
            }
            CigNodeKind::Leaf(v) => {
                writeln!(f, "{}{}{}", prefix, connector, v)
            }
            CigNodeKind::Internal { interaction, children } => {
                writeln!(f, "{}{}{}", prefix, connector, interaction)?;

                // Build prefix for children
                let child_prefix = if is_root {
                    String::new()
                } else {
                    format!("{}{}", prefix, if is_last { "   " } else { "│  " })
                };

                for (i, child) in children.iter().enumerate() {
                    let is_last_child = i == children.len() - 1;
                    child.display_tree(f, &child_prefix, is_last_child, false)?;
                }
                Ok(())
            }
        }
    }
}

/// The Canonical Interaction Graph.
///
/// A CIG is rooted at a single node and provides operations for
/// structural analysis and equivalence checking.
#[derive(Clone)]
pub struct Cig {
    /// The root node of the CIG.
    root: Arc<CigNode>,
}

impl Cig {
    /// Create a CIG from a root node.
    pub fn new(root: Arc<CigNode>) -> Self {
        Cig { root }
    }

    /// Get the root node.
    pub fn root(&self) -> &Arc<CigNode> {
        &self.root
    }

    /// Check if two CIGs represent equivalent functions.
    ///
    /// This is O(1) due to canonicity - just compare root hashes.
    pub fn equivalent(&self, other: &Cig) -> bool {
        self.root.hash == other.root.hash
    }

    /// Get the size (number of nodes).
    pub fn size(&self) -> usize {
        self.root.size()
    }

    /// Get the depth.
    pub fn depth(&self) -> usize {
        self.root.depth()
    }

    /// Get the interaction width.
    pub fn interaction_width(&self) -> usize {
        self.root.interaction_width()
    }

    /// Get the total interaction table size.
    pub fn table_size(&self) -> usize {
        self.root.table_size()
    }

    /// Get all variables.
    pub fn variables(&self) -> Vec<Var> {
        self.root.variables()
    }

    /// Get the canonical hash.
    pub fn canonical_hash(&self) -> u64 {
        self.root.hash
    }

    /// Extract the partition of variables represented by this CIG.
    pub fn extract_partition(&self) -> Partition {
        self.root.extract_partition()
    }
}

impl fmt::Debug for Cig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CIG({:?})", self.root)
    }
}

impl fmt::Display for Cig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CIG:")?;
        write!(f, "{}", self.root)
    }
}

impl PartialEq for Cig {
    fn eq(&self, other: &Self) -> bool {
        self.equivalent(other)
    }
}

impl Eq for Cig {}

impl std::hash::Hash for Cig {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.root.hash.hash(state);
    }
}

/// A unique table for hash-consing CIG nodes.
#[derive(Default)]
pub struct UniqueTable {
    /// Map from hash to nodes with that hash.
    table: FxHashMap<u64, Vec<Arc<CigNode>>>,
    /// Constant nodes (cached).
    zero: Option<Arc<CigNode>>,
    one: Option<Arc<CigNode>>,
}

impl UniqueTable {
    /// Create a new unique table.
    pub fn new() -> Self {
        UniqueTable::default()
    }

    /// Get or create the constant 0 node.
    pub fn zero(&mut self) -> Arc<CigNode> {
        if let Some(ref z) = self.zero {
            z.clone()
        } else {
            let z = Arc::new(CigNode::constant(false));
            self.zero = Some(z.clone());
            z
        }
    }

    /// Get or create the constant 1 node.
    pub fn one(&mut self) -> Arc<CigNode> {
        if let Some(ref o) = self.one {
            o.clone()
        } else {
            let o = Arc::new(CigNode::constant(true));
            self.one = Some(o.clone());
            o
        }
    }

    /// Get or create a leaf node.
    pub fn leaf(&mut self, var: Var) -> Arc<CigNode> {
        let node = CigNode::leaf(var);
        self.unique(node)
    }

    /// Get or create an internal node.
    pub fn internal(&mut self, interaction: InteractionFunction, children: Vec<Arc<CigNode>>) -> Arc<CigNode> {
        let node = CigNode::internal(interaction, children);
        self.unique(node)
    }

    /// Insert a node into the table, returning the canonical version.
    fn unique(&mut self, node: CigNode) -> Arc<CigNode> {
        let hash = node.hash;

        // Check if we already have this node
        if let Some(nodes) = self.table.get(&hash) {
            for existing in nodes {
                if existing.kind == node.kind {
                    return existing.clone();
                }
            }
        }

        // Create new node
        let arc = Arc::new(node);
        self.table.entry(hash).or_default().push(arc.clone());
        arc
    }

    /// Get statistics about the unique table.
    pub fn stats(&self) -> UniqueTableStats {
        let total_nodes: usize = self.table.values().map(|v| v.len()).sum();
        let total_buckets = self.table.len();

        UniqueTableStats {
            total_nodes,
            total_buckets,
        }
    }
}

/// Statistics about the unique table.
#[derive(Debug, Clone)]
pub struct UniqueTableStats {
    /// Total number of unique nodes.
    pub total_nodes: usize,
    /// Number of hash buckets.
    pub total_buckets: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_nodes() {
        let zero = CigNode::constant(false);
        let one = CigNode::constant(true);

        assert!(zero.is_constant());
        assert!(one.is_constant());
        assert_eq!(zero.as_constant(), Some(false));
        assert_eq!(one.as_constant(), Some(true));
    }

    #[test]
    fn test_leaf_nodes() {
        let x1 = CigNode::leaf(Var(1));
        let x2 = CigNode::leaf(Var(2));

        assert!(x1.is_leaf());
        assert_eq!(x1.as_leaf(), Some(Var(1)));
        assert_ne!(x1.canonical_hash(), x2.canonical_hash());
    }

    #[test]
    fn test_internal_nodes() {
        let x1 = Arc::new(CigNode::leaf(Var(1)));
        let x2 = Arc::new(CigNode::leaf(Var(2)));

        let and_i = InteractionFunction::from_operator(crate::Operator::And);
        let node = CigNode::internal(and_i, vec![x1, x2]);

        assert!(node.is_internal());
        assert_eq!(node.num_children(), 2);
    }

    #[test]
    fn test_unique_table() {
        let mut table = UniqueTable::new();

        let x1_a = table.leaf(Var(1));
        let x1_b = table.leaf(Var(1));

        // Should be the same Arc
        assert!(Arc::ptr_eq(&x1_a, &x1_b));

        let x2 = table.leaf(Var(2));
        assert!(!Arc::ptr_eq(&x1_a, &x2));
    }

    #[test]
    fn test_cig_equivalence() {
        let mut table = UniqueTable::new();

        let x1 = table.leaf(Var(1));
        let x2 = table.leaf(Var(2));

        let and_i = InteractionFunction::from_operator(crate::Operator::And);
        let node1 = table.internal(and_i.clone(), vec![x1.clone(), x2.clone()]);
        let node2 = table.internal(and_i, vec![x1, x2]);

        let cig1 = Cig::new(node1);
        let cig2 = Cig::new(node2);

        assert!(cig1.equivalent(&cig2));
        assert_eq!(cig1, cig2);
    }
}
