//! Automata-based abstract domain.
//!
//! This module implements a symbolic automata domain for string analysis.
//! Elements denote regular languages over Unicode strings, represented as (symbolic) DFAs whose
//! transitions are labeled by character predicates (e.g., character classes).
//!
//! ```text
//! Concretization: γ(A) ⊆ Σ*   (the language accepted by automaton A)
//! Order:          A1 ⊑ A2  iff  γ(A1) ⊆ γ(A2)
//! Join/Meet:      union / intersection of languages
//! ```

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::Rc;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;

use super::domain::AbstractDomain;

// ============================================================================
// Predicate Layer
// ============================================================================

/// A canonical, comparable predicate over the alphabet (Unicode scalar values).
///
/// Predicates are the labels on the edges of the symbolic automata.
/// They represent sets of characters.
pub trait Predicate: Clone + Eq + Debug {
    /// Is character `c` accepted by the predicate?
    fn contains(&self, c: char) -> bool;

    /// Conjunction (AND) of predicates.
    /// Returns a predicate representing the intersection of the two sets of characters.
    fn and(&self, other: &Self) -> Self;

    /// Disjunction (OR) of predicates.
    /// Returns a predicate representing the union of the two sets of characters.
    fn or(&self, other: &Self) -> Self;

    /// Negation (NOT).
    /// Returns a predicate representing the complement of the set of characters.
    fn not(&self) -> Self;

    /// Is predicate empty?
    /// Returns true if the predicate accepts no characters.
    fn is_empty(&self) -> bool;

    /// Produce a canonical string key useful for hashing / deterministic ordering.
    /// This key should uniquely identify the predicate content.
    fn canonical_key(&self) -> String;

    /// Compute a set of disjoint minterms (atomic predicates) from a list of predicates.
    ///
    /// The minterms partition the input space such that for any input `x` and any
    /// original predicate `p`, `p` either contains all of a minterm or none.
    fn compute_minterms(preds: &[Self]) -> Vec<Self>;
}

/// A simple character-class predicate represented as a set of disjoint ranges.
///
/// This struct implements `Predicate` by maintaining a sorted list of disjoint
/// character ranges (inclusive). It supports standard set operations (union, intersection, complement).
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct CharClass {
    // invariant: ranges are disjoint, sorted, non-adjacent
    ranges: Vec<(u32, u32)>,
}

impl CharClass {
    /// Create an empty character class (accepts nothing).
    pub fn empty() -> Self {
        CharClass { ranges: Vec::new() }
    }

    /// Create a full character class (accepts all Unicode characters).
    pub fn full() -> Self {
        CharClass {
            ranges: vec![(0, 0x10FFFF)],
        }
    }

    /// Create a character class from a list of ranges.
    /// The ranges do not need to be sorted or disjoint; they will be normalized.
    pub fn from_ranges(mut ranges: Vec<(u32, u32)>) -> Self {
        ranges.sort_unstable();
        let mut out = Vec::<(u32, u32)>::new();
        for (a, b) in ranges {
            if a > b {
                continue;
            }
            if let Some(last) = out.last_mut() {
                if a <= last.1 + 1 {
                    if b > last.1 {
                        last.1 = b;
                    }
                    continue;
                }
            }
            out.push((a, b));
        }
        CharClass { ranges: out }
    }

    /// Create a character class containing a single character.
    pub fn single(ch: char) -> Self {
        let u = ch as u32;
        CharClass { ranges: vec![(u, u)] }
    }

    /// Create a character class containing a range of characters [a, b].
    pub fn range(a: char, b: char) -> Self {
        CharClass::from_ranges(vec![(a as u32, b as u32)])
    }
}

impl Predicate for CharClass {
    fn contains(&self, c: char) -> bool {
        let u = c as u32;
        let mut lo = 0usize;
        let mut hi = self.ranges.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            let (s, e) = self.ranges[mid];
            if u < s {
                hi = mid;
            } else if u > e {
                lo = mid + 1;
            } else {
                return true;
            }
        }
        false
    }

    fn and(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        let mut i = 0usize;
        let mut j = 0usize;
        while i < self.ranges.len() && j < other.ranges.len() {
            let (a1, b1) = self.ranges[i];
            let (a2, b2) = other.ranges[j];
            let lo = a1.max(a2);
            let hi = b1.min(b2);
            if lo <= hi {
                out.push((lo, hi));
            }
            if b1 < b2 {
                i += 1;
            } else {
                j += 1;
            }
        }
        CharClass::from_ranges(out)
    }

    fn or(&self, other: &Self) -> Self {
        let mut all = self.ranges.clone();
        all.extend(other.ranges.iter());
        CharClass::from_ranges(all)
    }

    fn not(&self) -> Self {
        let mut out = Vec::new();
        let mut cur = 0u32;
        for (s, e) in &self.ranges {
            if cur < *s {
                out.push((cur, s - 1));
            }
            if *e == 0x10FFFF {
                cur = 0x110000;
                break;
            }
            cur = e + 1;
        }
        if cur <= 0x10FFFF {
            out.push((cur, 0x10FFFF));
        }
        CharClass::from_ranges(out)
    }

    fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    fn canonical_key(&self) -> String {
        let mut s = String::new();
        for (a, b) in &self.ranges {
            use std::fmt::Write;
            write!(&mut s, "{}-{};", a, b).unwrap();
        }
        s
    }

    fn compute_minterms(preds: &[Self]) -> Vec<Self> {
        let mut boundaries: BTreeSet<u32> = BTreeSet::new();

        for p in preds {
            for (a, b) in &p.ranges {
                boundaries.insert(*a);
                if *b < 0x10FFFF {
                    boundaries.insert(*b + 1);
                }
            }
        }

        if !boundaries.is_empty() {
            let vecb: Vec<u32> = boundaries.into_iter().collect();
            let mut atoms: Vec<(u32, u32)> = Vec::new();
            for i in 0..vecb.len() {
                let start = vecb[i];
                let end = if i + 1 < vecb.len() { vecb[i + 1] - 1 } else { 0x10FFFF };
                if start <= end {
                    atoms.push((start, end));
                }
            }

            let mut minterms: Vec<Self> = Vec::new();
            let mut seen_sigs: HashSet<Vec<bool>> = HashSet::new();

            for (s, _e) in atoms {
                let rep = std::char::from_u32(s).unwrap_or('\u{FFFD}');
                let mut sig = Vec::new();
                for p in preds {
                    sig.push(p.contains(rep));
                }

                if sig.iter().all(|&x| !x) {
                    continue;
                }
                if seen_sigs.contains(&sig) {
                    continue;
                }
                seen_sigs.insert(sig.clone());

                // Construct minterm from signature
                let mut m: Option<Self> = None;
                for (i, &b) in sig.iter().enumerate() {
                    let p = &preds[i];
                    let part = if b { p.clone() } else { p.not() };
                    m = Some(match m {
                        None => part,
                        Some(acc) => acc.and(&part),
                    });
                }
                if let Some(final_m) = m {
                    if !final_m.is_empty() {
                        minterms.push(final_m);
                    }
                }
            }
            return minterms;
        }
        Vec::new()
    }
}

/// A character predicate implemented using Binary Decision Diagrams (BDDs).
///
/// This implementation uses a shared BDD manager to represent sets of characters.
/// The 21 bits of a Unicode scalar value are mapped to BDD variables 1..21.
#[derive(Clone)]
pub struct BddCharPredicate {
    manager: Rc<Bdd>,
    node: Ref,
}

impl BddCharPredicate {
    /// Create a new BDD predicate from a BDD node and manager.
    pub fn new(manager: Rc<Bdd>, node: Ref) -> Self {
        BddCharPredicate { manager, node }
    }

    /// Create a predicate for a single character.
    pub fn single(manager: Rc<Bdd>, c: char) -> Self {
        let val = c as u32;
        let mut node = manager.one();
        // Encode bits 0..20 into variables 1..21
        // We build a cube (conjunction of literals)
        // Variable i corresponds to bit i-1
        for i in 1..=21 {
            let bit = (val >> (i - 1)) & 1;
            let var = manager.mk_var(i);
            let lit = if bit == 1 { var } else { manager.apply_not(var) };
            node = manager.apply_and(node, lit);
        }
        BddCharPredicate { manager, node }
    }

    /// Create a predicate for a range of characters [start, end].
    ///
    /// This implementation uses bit-blasting to efficiently construct the BDD
    /// for the range condition `start <= val <= end`.
    pub fn range(manager: Rc<Bdd>, start: char, end: char) -> Self {
        let s = start as u32;
        let e = end as u32;

        // range(a, b) = (val >= a) AND (val <= b)
        let ge_start = Self::build_ge(&manager, s);
        let le_end = Self::build_le(&manager, e);
        let node = manager.apply_and(ge_start, le_end);

        BddCharPredicate { manager, node }
    }

    /// Build BDD for val >= limit
    fn build_ge(manager: &Rc<Bdd>, limit: u32) -> Ref {
        // We construct the BDD for `val >= limit` by iterating from LSB to MSB.
        //
        // The logic is based on the recursive definition:
        // GE(i, limit) =
        //   if limit[i] == 1: v_i=1 AND GE(i-1, limit)
        //   if limit[i] == 0: v_i=1 OR GE(i-1, limit)
        //
        // Base case: GE(-1, limit) = 1 (since we covered all bits and they were equal)
        //
        // We iterate i from 0 to 20, building the BDD bottom-up.

        let mut res = manager.one(); // True for the "equal" case at the end (val == limit is >= limit)

        for i in 0..21 {
            let bit_idx = i;
            let var_idx = i + 1;
            let var = manager.mk_var(var_idx);
            let limit_bit = (limit >> bit_idx) & 1;

            if limit_bit == 1 {
                // If limit has 1, we must have 1 to be equal, or if we have 0 we are smaller (fail).
                // So we need v_i=1 AND result_from_lower_bits
                res = manager.apply_and(var, res);
            } else {
                // If limit has 0, if we have 1 we are greater (success immediately).
                // If we have 0, we are equal so far, check lower bits.
                // So v_i=1 OR result_from_lower_bits
                res = manager.apply_or(var, res);
            }
        }
        res
    }

    /// Build BDD for val <= limit
    fn build_le(manager: &Rc<Bdd>, limit: u32) -> Ref {
        // We construct the BDD for `val <= limit` by iterating from LSB to MSB.
        //
        // The logic is symmetric to build_ge:
        // LE(i, limit) =
        //   if limit[i] == 0: v_i=0 AND LE(i-1, limit)
        //   if limit[i] == 1: v_i=0 OR LE(i-1, limit)

        let mut res = manager.one();

        for i in 0..21 {
            let bit_idx = i;
            let var_idx = i + 1;
            let var = manager.mk_var(var_idx);
            let limit_bit = (limit >> bit_idx) & 1;

            if limit_bit == 0 {
                // limit is 0. If v_i is 1, we are greater (fail).
                // Must be 0.
                let not_var = manager.apply_not(var);
                res = manager.apply_and(not_var, res);
            } else {
                // limit is 1. If v_i is 0, we are smaller (success).
                // If v_i is 1, check lower.
                let not_var = manager.apply_not(var);
                res = manager.apply_or(not_var, res);
            }
        }
        res
    }
}

impl PartialEq for BddCharPredicate {
    fn eq(&self, other: &Self) -> bool {
        // Assume they share the same manager.
        // If not, this comparison is invalid, but we can't easily check manager equality (Rc ptr eq).
        // For safety in this example, we assume correct usage.
        self.node == other.node
    }
}

impl Eq for BddCharPredicate {}

impl Debug for BddCharPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "BddPred({})", self.node)
    }
}

impl Predicate for BddCharPredicate {
    fn contains(&self, c: char) -> bool {
        let val = c as u32;
        let mut curr = self.node;
        // Traverse the BDD
        while !self.manager.is_terminal(curr) {
            let var_idx = self.manager.variable(curr.id()).id();
            if var_idx > 21 {
                // Should not happen for char predicates
                return false;
            }
            let bit_idx = var_idx - 1;
            let bit = (val >> bit_idx) & 1;
            if bit == 1 {
                curr = self.manager.high_node(curr);
            } else {
                curr = self.manager.low_node(curr);
            }
        }
        self.manager.is_one(curr)
    }

    fn and(&self, other: &Self) -> Self {
        let node = self.manager.apply_and(self.node, other.node);
        BddCharPredicate {
            manager: self.manager.clone(),
            node,
        }
    }

    fn or(&self, other: &Self) -> Self {
        let node = self.manager.apply_or(self.node, other.node);
        BddCharPredicate {
            manager: self.manager.clone(),
            node,
        }
    }

    fn not(&self) -> Self {
        let node = self.manager.apply_not(self.node);
        BddCharPredicate {
            manager: self.manager.clone(),
            node,
        }
    }

    fn is_empty(&self) -> bool {
        self.manager.is_zero(self.node)
    }

    fn canonical_key(&self) -> String {
        // BDD node index is canonical within the manager.
        self.node.id().to_string()
    }

    fn compute_minterms(preds: &[Self]) -> Vec<Self> {
        if preds.is_empty() {
            return Vec::new();
        }
        // All preds share the same manager (assumed)
        let manager = preds[0].manager.clone();

        let mut partition = vec![BddCharPredicate::new(manager.clone(), manager.one())];

        for p in preds {
            let mut next_partition = Vec::new();
            for m in partition {
                let m_and_p = m.and(p);
                let m_and_not_p = m.and(&p.not());

                if !m_and_p.is_empty() {
                    next_partition.push(m_and_p);
                }
                if !m_and_not_p.is_empty() {
                    next_partition.push(m_and_not_p);
                }
            }
            partition = next_partition;
        }

        // Filter out regions where no predicate holds
        let union_all = preds
            .iter()
            .fold(BddCharPredicate::new(manager.clone(), manager.zero()), |acc, p| acc.or(p));

        partition.retain(|m| !m.and(&union_all).is_empty());

        partition
    }
}

impl PartialOrd for BddCharPredicate {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BddCharPredicate {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by node index and negation (arbitrary but consistent ordering).
        let i1 = self.node.id().raw();
        let i2 = other.node.id().raw();
        match i1.cmp(&i2) {
            std::cmp::Ordering::Equal => self.node.is_negated().cmp(&other.node.is_negated()),
            ord => ord,
        }
    }
}

// ============================================================================
// Automata Core
// ============================================================================

pub type StateId = usize;

/// A symbolic transition in an automaton.
///
/// Represents a transition from a source state (implicit) to a `target` state,
/// guarded by a predicate `label`. If the predicate contains the input character,
/// the transition can be taken.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolicTransition<P: Predicate> {
    pub label: P,
    pub target: StateId,
}

/// Deterministic symbolic automaton (DFA).
///
/// A DFA consists of a set of states, a set of accepting states, and a transition function.
/// In a symbolic DFA, transitions are labeled with predicates rather than single characters.
/// For any state and any character, there must be at most one applicable transition (determinism).
///
/// This implementation allows partial DFAs (where some characters might have no transition),
/// which implicitly lead to a non-accepting sink state.
#[derive(Clone, Debug)]
pub struct SymbolicDFA<P: Predicate> {
    pub states: usize,
    pub accepting: Vec<bool>,
    pub transitions: Vec<Vec<SymbolicTransition<P>>>,
}

impl<P: Predicate> PartialEq for SymbolicDFA<P> {
    fn eq(&self, other: &Self) -> bool {
        // Structural equality check
        if self.states != other.states {
            return false;
        }
        if self.accepting != other.accepting {
            return false;
        }
        for i in 0..self.states {
            let ta = &self.transitions[i];
            let tb = &other.transitions[i];
            if ta.len() != tb.len() {
                return false;
            }
            for (a, b) in ta.iter().zip(tb.iter()) {
                if a.target != b.target {
                    return false;
                }
                if a.label.canonical_key() != b.label.canonical_key() {
                    return false;
                }
            }
        }
        true
    }
}

impl<P: Predicate> SymbolicDFA<P> {
    /// Create a new DFA with `states` number of states.
    /// Initially, no states are accepting and there are no transitions.
    pub fn new(states: usize) -> Self {
        SymbolicDFA {
            states,
            accepting: vec![false; states],
            transitions: vec![Vec::new(); states],
        }
    }

    /// Check if the DFA accepts the given string `input`.
    pub fn accepts(&self, input: &str) -> bool {
        let mut cur = 0usize;
        for ch in input.chars() {
            let mut found = false;
            for tr in &self.transitions[cur] {
                if tr.label.contains(ch) {
                    cur = tr.target;
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        self.accepting[cur]
    }

    /// Compute the complement of the language accepted by this DFA.
    ///
    /// This operation first completes the DFA (making it total) and then flips
    /// the accepting status of all states.
    pub fn complement(&self, universe: P) -> Self
    where
        P: Clone + Ord,
    {
        let mut out = self.clone();
        out.complete(universe);
        for a in &mut out.accepting {
            *a = !*a;
        }
        out
    }

    /// Make the DFA complete (total).
    ///
    /// Adds a sink state and transitions to it for any character that doesn't
    /// have a defined transition from a state.
    pub fn complete(&mut self, universe: P)
    where
        P: Clone + Ord,
    {
        let n = self.states;
        let mut new_transitions: Vec<(usize, P)> = Vec::new();

        for i in 0..n {
            let mut union_pred: Option<P> = None;
            for tr in &self.transitions[i] {
                union_pred = Some(match union_pred {
                    None => tr.label.clone(),
                    Some(acc) => acc.or(&tr.label),
                });
            }

            let missing = match union_pred {
                Some(u) => u.not(),
                None => universe.clone(),
            };

            if !missing.is_empty() {
                new_transitions.push((i, missing));
            }
        }

        if !new_transitions.is_empty() {
            let sid = self.states;
            self.states += 1;
            self.accepting.push(false);
            self.transitions.push(Vec::new());
            // Sink loops to itself on full
            self.transitions[sid].push(SymbolicTransition {
                label: universe,
                target: sid,
            });

            for (src, label) in new_transitions {
                self.transitions[src].push(SymbolicTransition { label, target: sid });
                self.transitions[src].sort_by_key(|tr| tr.label.canonical_key());
            }
        }
    }

    /// Check if the language is empty (reachability of accepting states).
    pub fn is_empty_lang(&self) -> bool {
        let mut visited = HashSet::new();
        let mut q = VecDeque::new();
        q.push_back(0);
        visited.insert(0);

        while let Some(s) = q.pop_front() {
            if self.accepting[s] {
                return false;
            }
            for tr in &self.transitions[s] {
                if !visited.contains(&tr.target) {
                    visited.insert(tr.target);
                    q.push_back(tr.target);
                }
            }
        }
        true
    }

    /// Check if language is full (complement is empty).
    pub fn is_full_lang(&self, universe: P) -> bool
    where
        P: Clone + Ord,
    {
        // Note: this assumes the DFA is complete (total).
        // If not complete, we should first complete it or check for missing transitions.
        // For simplicity, we assume completeness or use complement().is_empty_lang().
        // But complement() just flips accepting bits, so it relies on completeness.
        // Let's use complement().is_empty_lang() assuming completeness.
        self.complement(universe).is_empty_lang()
    }
}

// ============================================================================
// NFA Builder & Algorithms
// ============================================================================

/// Nondeterministic symbolic automaton (NFA).
///
/// Used primarily as a builder for DFAs. It supports multiple transitions on the same
/// character from a single state, and epsilon transitions are not explicitly supported
/// (though one could model them, this implementation focuses on character-based transitions).
#[derive(Clone, Debug)]
pub struct SymbolicNFA<P: Predicate> {
    pub start: StateId,
    pub states: usize,
    pub accepting: Vec<bool>,
    pub transitions: Vec<Vec<SymbolicTransition<P>>>,
}

impl<P: Predicate> SymbolicNFA<P> {
    /// Create a new NFA with a single start state (0).
    pub fn new() -> Self {
        SymbolicNFA {
            start: 0,
            states: 1,
            accepting: vec![false],
            transitions: vec![Vec::new()],
        }
    }

    /// Add a new state to the NFA.
    /// Returns the ID of the new state.
    pub fn add_state(&mut self, accepting: bool) -> StateId {
        let id = self.states;
        self.states += 1;
        self.accepting.push(accepting);
        self.transitions.push(Vec::new());
        id
    }

    /// Add a transition from `from` to `to` labeled with `pred`.
    pub fn add_transition(&mut self, from: StateId, pred: P, to: StateId) {
        self.transitions[from].push(SymbolicTransition { label: pred, target: to });
    }

    /// Convert the NFA to an equivalent DFA using the subset construction algorithm.
    ///
    /// This process involves:
    /// 1. Collecting all predicates from transitions.
    /// 2. Generating a set of disjoint "minterms" (atomic predicates) that partition the input space.
    /// 3. Performing the standard subset construction using these minterms as the alphabet.
    pub fn determinize(&self) -> SymbolicDFA<P>
    where
        P: Clone + Ord,
    {
        let mut preds: Vec<P> = Vec::new();
        for trs in &self.transitions {
            for tr in trs {
                preds.push(tr.label.clone());
            }
        }
        if preds.is_empty() {
            let mut dfa = SymbolicDFA::new(1);
            dfa.accepting[0] = self.accepting[self.start];
            return dfa;
        }

        let minterms = P::compute_minterms(&preds);
        let n = self.states;
        let mcount = minterms.len();
        let mut reach: Vec<Vec<Vec<StateId>>> = vec![vec![Vec::new(); mcount]; n];
        for s in 0..n {
            for tr in &self.transitions[s] {
                for (mi, mt) in minterms.iter().enumerate() {
                    if !tr.label.and(mt).is_empty() {
                        reach[s][mi].push(tr.target);
                    }
                }
            }
        }

        let mut dfa_states: Vec<Vec<StateId>> = Vec::new();
        let mut dfa_index: HashMap<Vec<StateId>, StateId> = HashMap::new();
        let mut q = VecDeque::new();

        let start_set = vec![self.start];
        dfa_states.push(start_set.clone());
        dfa_index.insert(start_set.clone(), 0usize);
        q.push_back(0usize);

        while let Some(did) = q.pop_front() {
            let nset = dfa_states[did].clone();
            for (mi, _) in minterms.iter().enumerate() {
                let mut target_set: Vec<StateId> = Vec::new();
                for &s in &nset {
                    for &t in &reach[s][mi] {
                        if !target_set.contains(&t) {
                            target_set.push(t);
                        }
                    }
                }
                if target_set.is_empty() {
                    continue;
                }
                target_set.sort_unstable();
                if !dfa_index.contains_key(&target_set) {
                    let tid = dfa_states.len();
                    dfa_index.insert(target_set.clone(), tid);
                    dfa_states.push(target_set.clone());
                    q.push_back(tid);
                }
            }
        }

        let mut dfa = SymbolicDFA::new(dfa_states.len());
        for (i, set) in dfa_states.iter().enumerate() {
            dfa.accepting[i] = set.iter().any(|&s| self.accepting[s]);
        }

        for (i, set) in dfa_states.iter().enumerate() {
            for (mi, mt) in minterms.iter().enumerate() {
                let mut target_set: Vec<StateId> = Vec::new();
                for &s in set {
                    for &t in &reach[s][mi] {
                        if !target_set.contains(&t) {
                            target_set.push(t);
                        }
                    }
                }
                if target_set.is_empty() {
                    continue;
                }
                target_set.sort_unstable();
                let tid = dfa_index[&target_set];
                dfa.transitions[i].push(SymbolicTransition {
                    label: mt.clone(),
                    target: tid,
                });
            }
            dfa.transitions[i].sort_by_key(|tr| tr.label.canonical_key());
        }

        dfa
    }
}

/// Minimize a DFA using Hopcroft's algorithm (or a variation suitable for symbolic automata).
///
/// This implementation uses a partition refinement algorithm.
pub fn minimize_dfa<P: Predicate + Clone + Ord>(dfa: &SymbolicDFA<P>) -> SymbolicDFA<P> {
    let n = dfa.states;
    let mut part: Vec<usize> = vec![0; n];
    let mut blocks: Vec<Vec<StateId>> = Vec::new();
    let mut b_accept: Vec<StateId> = Vec::new();
    let mut b_non: Vec<StateId> = Vec::new();
    for i in 0..n {
        if dfa.accepting[i] {
            b_accept.push(i);
        } else {
            b_non.push(i);
        }
    }
    if !b_accept.is_empty() {
        blocks.push(b_accept.clone());
    }
    if !b_non.is_empty() {
        blocks.push(b_non.clone());
    }
    for (idx, b) in blocks.iter().enumerate() {
        for &s in b {
            part[s] = idx;
        }
    }

    let mut global_labels: Vec<P> = Vec::new();
    let mut seen = HashSet::new();
    for trs in &dfa.transitions {
        for t in trs {
            let key = t.label.canonical_key();
            if !seen.contains(&key) {
                seen.insert(key.clone());
                global_labels.push(t.label.clone());
            }
        }
    }

    let mut rev: HashMap<String, Vec<Vec<StateId>>> = HashMap::new();
    for lab in &global_labels {
        let key = lab.canonical_key();
        rev.insert(key.clone(), vec![Vec::new(); n]);
    }
    for r in 0..n {
        for tr in &dfa.transitions[r] {
            let key = tr.label.canonical_key();
            rev.get_mut(&key).unwrap()[tr.target].push(r);
        }
    }

    let mut work: VecDeque<(usize, String)> = VecDeque::new();
    for (i, _block) in blocks.iter().enumerate() {
        for lab in &global_labels {
            work.push_back((i, lab.canonical_key()));
        }
    }

    while let Some((a_idx, lab_key)) = work.pop_front() {
        if a_idx >= blocks.len() {
            continue;
        } // Block might have been split/moved? No, indices are stable-ish?
          // Actually, blocks are only appended. But if we split a block, we modify it in place and add a new one.

        let pre = &rev[&lab_key];
        let mut involved: Vec<StateId> = Vec::new();
        for &q in &blocks[a_idx] {
            for &p in &pre[q] {
                if !involved.contains(&p) {
                    involved.push(p);
                }
            }
        }
        if involved.is_empty() {
            continue;
        }

        let mut new_blocks: Vec<(usize, Vec<StateId>, Vec<StateId>)> = Vec::new();
        for (i, b) in blocks.iter().enumerate() {
            let mut b1 = Vec::new();
            let mut b2 = Vec::new();
            for &q in b {
                if involved.contains(&q) {
                    b1.push(q);
                } else {
                    b2.push(q);
                }
            }
            if !b1.is_empty() && !b2.is_empty() {
                new_blocks.push((i, b1, b2));
            }
        }

        for (bi, b1, b2) in new_blocks {
            blocks[bi] = b1.clone();
            let new_idx = blocks.len();
            blocks.push(b2.clone());
            for &s in &blocks[bi] {
                part[s] = bi;
            }
            for &s in &blocks[new_idx] {
                part[s] = new_idx;
            }
            for lab in &global_labels {
                work.push_back((new_idx, lab.canonical_key()));
            }
        }
    }

    let mut block_reps: Vec<(usize, StateId)> = blocks.iter().enumerate().map(|(i, b)| (i, *b.iter().min().unwrap())).collect();
    block_reps.sort_by_key(|(_, rep)| *rep);
    let mut mapping: Vec<usize> = vec![0; blocks.len()];
    for (new_idx, (old_idx, _rep)) in block_reps.iter().enumerate() {
        mapping[*old_idx] = new_idx;
    }

    let new_n = blocks.len();
    let mut out = SymbolicDFA::<P>::new(new_n);
    for (old_idx, block) in blocks.iter().enumerate() {
        let new_idx = mapping[old_idx];
        out.accepting[new_idx] = block.iter().any(|&s| dfa.accepting[s]);
    }

    for (old_idx, block) in blocks.iter().enumerate() {
        let new_idx = mapping[old_idx];
        let rep = *block.iter().min().unwrap();
        for tr in &dfa.transitions[rep] {
            let tgt_block = part[tr.target];
            let new_tgt = mapping[tgt_block];
            if !out.transitions[new_idx]
                .iter()
                .any(|e| e.target == new_tgt && e.label.canonical_key() == tr.label.canonical_key())
            {
                out.transitions[new_idx].push(SymbolicTransition {
                    label: tr.label.clone(),
                    target: new_tgt,
                });
            }
        }
        out.transitions[new_idx].sort_by_key(|t| t.label.canonical_key());
    }

    out
}

impl<P: Predicate + Clone + Ord> SymbolicDFA<P> {
    /// Compute the union of two DFAs.
    /// Returns a DFA that accepts a string if either input DFA accepts it.
    pub fn union(&self, other: &SymbolicDFA<P>) -> SymbolicDFA<P> {
        self.product(other, |a, b| a || b)
    }

    /// Compute the intersection of two DFAs.
    /// Returns a DFA that accepts a string if both input DFAs accept it.
    pub fn intersection(&self, other: &SymbolicDFA<P>) -> SymbolicDFA<P> {
        self.product(other, |a, b| a && b)
    }

    fn product<F>(&self, other: &SymbolicDFA<P>, accept_op: F) -> SymbolicDFA<P>
    where
        F: Fn(bool, bool) -> bool,
    {
        let mut labels: Vec<P> = Vec::new();
        let mut seen = HashSet::new();
        for trs in &self.transitions {
            for t in trs {
                let k = t.label.canonical_key();
                if seen.insert(k.clone()) {
                    labels.push(t.label.clone());
                }
            }
        }
        for trs in &other.transitions {
            for t in trs {
                let k = t.label.canonical_key();
                if seen.insert(k.clone()) {
                    labels.push(t.label.clone());
                }
            }
        }
        let minterms = P::compute_minterms(&labels);

        let mut index: HashMap<(StateId, StateId), StateId> = HashMap::new();
        let mut states: Vec<(StateId, StateId)> = Vec::new();
        let mut q = VecDeque::new();
        index.insert((0, 0), 0);
        states.push((0, 0));
        q.push_back(0usize);

        while let Some(id) = q.pop_front() {
            let (a, b) = states[id];
            for mt in &minterms {
                let t1 = if a == usize::MAX { None } else { self.transition_on_symbol(a, mt) };
                let t2 = if b == usize::MAX { None } else { other.transition_on_symbol(b, mt) };
                if t1.is_none() && t2.is_none() {
                    continue;
                }
                let t1v = t1.unwrap_or(usize::MAX);
                let t2v = t2.unwrap_or(usize::MAX);
                let real_pair = (t1v, t2v);
                if !index.contains_key(&real_pair) {
                    let nid = states.len();
                    index.insert(real_pair, nid);
                    states.push(real_pair);
                    q.push_back(nid);
                }
            }
        }

        let new_n = states.len();
        let mut out = SymbolicDFA::new(new_n);
        for (i, &(q1, q2)) in states.iter().enumerate() {
            let a1 = if q1 != usize::MAX { self.accepting[q1] } else { false };
            let a2 = if q2 != usize::MAX { other.accepting[q2] } else { false };
            out.accepting[i] = accept_op(a1, a2);
        }
        for (i, (q1, q2)) in states.iter().enumerate() {
            for mt in &minterms {
                let t1 = if *q1 == usize::MAX {
                    None
                } else {
                    self.transition_on_symbol(*q1, mt)
                };
                let t2 = if *q2 == usize::MAX {
                    None
                } else {
                    other.transition_on_symbol(*q2, mt)
                };
                if t1.is_none() && t2.is_none() {
                    continue;
                }
                let p1 = t1.unwrap_or(usize::MAX);
                let p2 = t2.unwrap_or(usize::MAX);
                let tid = index[&(p1, p2)];
                out.transitions[i].push(SymbolicTransition {
                    label: mt.clone(),
                    target: tid,
                });
            }
            out.transitions[i].sort_by_key(|tr| tr.label.canonical_key());
        }
        out
    }

    fn transition_on_symbol(&self, q: StateId, sym: &P) -> Option<StateId> {
        for tr in &self.transitions[q] {
            if !tr.label.and(sym).is_empty() {
                return Some(tr.target);
            }
        }
        None
    }
}

// ============================================================================
// Abstract Domain Implementation
// ============================================================================

/// The symbolic automata abstract domain.
///
/// Elements of this domain are symbolic DFAs representing regular languages.
/// The lattice operations are defined as follows:
/// - `bottom` (`⊥`): Empty language.
/// - `top` (`⊤`): Universal language (all strings).
/// - `join` (`⊔`): Union of languages (minimized).
/// - `meet` (`⊓`): Intersection of languages (minimized).
/// - `le` (`⊑`): Subset inclusion check.
#[derive(Clone, Debug)]
pub struct AutomataDomain;

impl AbstractDomain for AutomataDomain {
    type Element = SymbolicDFA<CharClass>;

    fn bottom(&self) -> Self::Element {
        // Empty language: 1 state, not accepting
        SymbolicDFA::new(1)
    }

    fn top(&self) -> Self::Element {
        // All strings: 1 state, accepting, transition on all chars to self
        let mut dfa = SymbolicDFA::new(1);
        dfa.accepting[0] = true;
        dfa.transitions[0].push(SymbolicTransition {
            label: CharClass::full(),
            target: 0,
        });
        dfa
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        elem.is_empty_lang()
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        elem.is_full_lang(CharClass::full())
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        // L1 <= L2 iff L1 subset L2 iff L1 intersect (not L2) is empty
        let not_l2 = elem2.complement(CharClass::full());
        let intersection = elem1.intersection(&not_l2);
        intersection.is_empty_lang()
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let union = elem1.union(elem2);
        minimize_dfa(&union)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        let intersection = elem1.intersection(elem2);
        minimize_dfa(&intersection)
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For now, just use join (union).
        // In a real implementation, we would need a widening operator to ensure termination
        // (e.g., state merging based on k-equivalence or similar).
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_automata_domain() {
        let domain = AutomataDomain;
        let bottom = domain.bottom();
        let top = domain.top();

        assert!(domain.is_bottom(&bottom));
        assert!(domain.is_top(&top));
        assert!(domain.le(&bottom, &top));
        assert!(!domain.le(&top, &bottom));

        // Create DFA for "a"
        let mut nfa_a = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa_a.add_state(true);
        nfa_a.add_transition(s0, CharClass::single('a'), s1);
        let dfa_a = nfa_a.determinize();

        // Create DFA for "b"
        let mut nfa_b = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa_b.add_state(true);
        nfa_b.add_transition(s0, CharClass::single('b'), s1);
        let dfa_b = nfa_b.determinize();

        // Join: "a" | "b"
        let joined = domain.join(&dfa_a, &dfa_b);
        assert!(joined.accepts("a"));
        assert!(joined.accepts("b"));
        assert!(!joined.accepts("c"));
        assert!(!joined.accepts("ab"));

        // Meet: "a" & "b" -> empty
        let met = domain.meet(&dfa_a, &dfa_b);
        assert!(domain.is_bottom(&met));
    }

    #[test]
    fn test_char_class_ops() {
        let c_a = CharClass::single('a');
        let c_b = CharClass::single('b');
        let c_ab = c_a.or(&c_b);

        assert!(c_ab.contains('a'));
        assert!(c_ab.contains('b'));
        assert!(!c_ab.contains('c'));

        let c_not_a = c_a.not();
        assert!(!c_not_a.contains('a'));
        assert!(c_not_a.contains('b'));
        assert!(c_not_a.contains('z'));

        let c_range = CharClass::range('a', 'z');
        assert!(c_range.contains('m'));
        assert!(!c_range.contains('A'));

        let c_intersect = c_range.and(&c_ab);
        assert!(c_intersect.contains('a'));
        assert!(c_intersect.contains('b'));
        assert!(!c_intersect.contains('c'));
    }

    #[test]
    fn test_dfa_operations() {
        // DFA for "a*"
        let mut nfa = SymbolicNFA::new();
        let s0 = 0;
        nfa.accepting[s0] = true;
        nfa.add_transition(s0, CharClass::single('a'), s0);
        let dfa = nfa.determinize();

        assert!(dfa.accepts(""));
        assert!(dfa.accepts("a"));
        assert!(dfa.accepts("aaaa"));
        assert!(!dfa.accepts("b"));
        assert!(!dfa.accepts("ab"));

        let dfa_compl = dfa.complement(CharClass::full());
        assert!(!dfa_compl.accepts("aaaa"));
        assert!(dfa_compl.accepts("b"));
    }

    #[test]
    fn test_automata_domain_complex() {
        let domain = AutomataDomain;

        // L1 = "a+"
        let mut nfa1 = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa1.add_state(true);
        nfa1.add_transition(s0, CharClass::single('a'), s1);
        nfa1.add_transition(s1, CharClass::single('a'), s1);
        let dfa1 = nfa1.determinize();

        // L2 = "b+"
        let mut nfa2 = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa2.add_state(true);
        nfa2.add_transition(s0, CharClass::single('b'), s1);
        nfa2.add_transition(s1, CharClass::single('b'), s1);
        let dfa2 = nfa2.determinize();

        // Join: "a+" | "b+"
        let joined = domain.join(&dfa1, &dfa2);
        assert!(joined.accepts("a"));
        assert!(joined.accepts("aaa"));
        assert!(joined.accepts("b"));
        assert!(joined.accepts("bbb"));
        assert!(!joined.accepts("ab"));
        assert!(!joined.accepts(""));

        // Meet: "a+" & "b+" -> empty
        let met = domain.meet(&dfa1, &dfa2);
        assert!(domain.is_bottom(&met));

        // L3 = "a"
        let mut nfa3 = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa3.add_state(true);
        nfa3.add_transition(s0, CharClass::single('a'), s1);
        let dfa3 = nfa3.determinize();

        // L3 <= L1 ("a" is in "a+")
        assert!(domain.le(&dfa3, &dfa1));
        // L1 !<= L3 ("aa" is in "a+" but not in "a")
        assert!(!domain.le(&dfa1, &dfa3));
    }

    #[test]
    fn test_dfa_complete_complement() {
        // DFA for "a" (incomplete)
        // 0 --a--> 1 (accepting)
        // Missing: 0 --[^a]--> ?, 1 --[.]--> ?
        let mut nfa = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa.add_state(true);
        nfa.add_transition(s0, CharClass::single('a'), s1);
        let dfa = nfa.determinize();

        assert!(dfa.accepts("a"));
        assert!(!dfa.accepts("b"));
        assert!(!dfa.accepts("aa"));

        // Complement of "a" should accept "b", "aa", "", etc.
        let dfa_compl = dfa.complement(CharClass::full());

        assert!(!dfa_compl.accepts("a"));
        assert!(dfa_compl.accepts("b"));
        assert!(dfa_compl.accepts("aa"));
        assert!(dfa_compl.accepts(""));

        // Check if dfa_compl is complete (it should be, because complement calls complete)
        // We can check if it has a sink state.
        // Original had 2 states. Complete adds 1 sink.
        // So dfa_compl should have at least 3 states (or 2 if it reused states, but implementation adds new state).
        assert!(dfa_compl.states >= 2);
    }

    #[test]
    fn test_automata_lattice_axioms() {
        use crate::domain::tests::test_lattice_axioms;
        let domain = AutomataDomain;

        // Helper to make DFA for single char
        let make_char = |c: char| {
            let mut nfa = SymbolicNFA::new();
            let s1 = nfa.add_state(true);
            nfa.add_transition(0, CharClass::single(c), s1);
            nfa.determinize()
        };

        let samples = vec![
            domain.bottom(),
            domain.top(),
            make_char('a'),
            make_char('b'),
            domain.join(&make_char('a'), &make_char('b')), // "a" | "b"
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_bdd_predicate() {
        let manager = Rc::new(Bdd::default());

        // Single char 'a'
        let p_a = BddCharPredicate::single(manager.clone(), 'a');
        assert!(p_a.contains('a'));
        assert!(!p_a.contains('b'));

        // Single char 'b'
        let p_b = BddCharPredicate::single(manager.clone(), 'b');
        assert!(p_b.contains('b'));
        assert!(!p_b.contains('a'));

        // Union: 'a' | 'b'
        let p_ab = p_a.or(&p_b);
        assert!(p_ab.contains('a'));
        assert!(p_ab.contains('b'));
        assert!(!p_ab.contains('c'));

        // Intersection: 'a' & 'b' -> empty
        let p_and = p_a.and(&p_b);
        assert!(p_and.is_empty());

        // Not 'a'
        let p_not_a = p_a.not();
        assert!(!p_not_a.contains('a'));
        assert!(p_not_a.contains('b'));

        // Range 'a'..'c'
        let p_range = BddCharPredicate::range(manager.clone(), 'a', 'c');
        assert!(p_range.contains('a'));
        assert!(p_range.contains('b'));
        assert!(p_range.contains('c'));
        assert!(!p_range.contains('d'));

        // DFA with BDD predicates
        let mut nfa = SymbolicNFA::new();
        let s0 = 0;
        let s1 = nfa.add_state(true);
        nfa.add_transition(s0, p_a.clone(), s1);
        let dfa = nfa.determinize();

        assert!(dfa.accepts("a"));
        assert!(!dfa.accepts("b"));

        // Complement DFA
        // We need a "full" predicate for complement
        // Let's use range 0..10FFFF as full, or just BddCharPredicate::range(..., '\0', '\u{10FFFF}')
        // Or simpler: BddCharPredicate::new(manager, manager.one)
        let full = BddCharPredicate::new(manager.clone(), manager.one());
        let dfa_compl = dfa.complement(full);
        assert!(!dfa_compl.accepts("a"));
        assert!(dfa_compl.accepts("b"));
    }
}
