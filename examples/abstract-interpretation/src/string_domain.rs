//! String abstract domains.
//!
//! This module provides abstract domains for analyzing string values.
//!
//! # Domains
//!
//! - [`StringConstantDomain`]: Tracks exact string values (flat lattice).
//! - [`StringLengthDomain`]: Tracks string lengths using intervals.
//! - [`StringPrefixDomain`]: Tracks known prefixes.
//! - [`StringSuffixDomain`]: Tracks known suffixes.
//! - [`StringInclusionDomain`]: Tracks required substrings.
//! - [`CharacterSetDomain`]: Tracks set of characters present.
//! - [`TaintDomain`]: Tracks taint status (security).
//! - [`StringCaseDomain`]: Tracks string casing (normalization).
//! - [`StringNumericDomain`]: Tracks numeric validity.

use std::collections::BTreeSet;
use std::fmt::Debug;

use crate::domain::AbstractDomain;
use crate::expr::{NumExpr, NumPred};
use crate::interval::{Interval, IntervalDomain, IntervalElement};
use crate::numeric::NumericDomain;

/// Represents a string value in the constant domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringConst {
    /// Bottom: Unreachable / Empty set
    Bottom,
    /// Top: Any string
    Top,
    /// Constant: A specific string value
    Constant(String),
}

/// String Constant Domain.
///
/// A flat lattice where elements are ordered as:
/// - `⊥ ⊑ Constant(s) ⊑ ⊤`
/// - `Constant(s₁) ⊑ Constant(s₂) ⟺ s₁ == s₂`
#[derive(Clone, Debug)]
pub struct StringConstantDomain;

impl StringConstantDomain {
    /// Concatenate two abstract string values.
    /// "hello" + "world" = "helloworld"
    pub fn concat(&self, elem1: &StringConst, elem2: &StringConst) -> StringConst {
        match (elem1, elem2) {
            // If either input is Bottom (unreachable), result is Bottom
            (StringConst::Bottom, _) | (_, StringConst::Bottom) => StringConst::Bottom,
            // If both are known constants, we can compute the result
            (StringConst::Constant(s1), StringConst::Constant(s2)) => StringConst::Constant(format!("{}{}", s1, s2)),
            // If either is Top (unknown), the result is unknown
            _ => StringConst::Top,
        }
    }
}

impl AbstractDomain for StringConstantDomain {
    type Element = StringConst;

    fn bottom(&self) -> Self::Element {
        StringConst::Bottom
    }

    fn top(&self) -> Self::Element {
        StringConst::Top
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringConst::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringConst::Top)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringConst::Bottom, _) => true,
            (_, StringConst::Top) => true,
            (StringConst::Constant(s1), StringConst::Constant(s2)) => s1 == s2,
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringConst::Bottom, e) | (e, StringConst::Bottom) => e.clone(),
            (StringConst::Top, _) | (_, StringConst::Top) => StringConst::Top,
            (StringConst::Constant(s1), StringConst::Constant(s2)) => {
                if s1 == s2 {
                    StringConst::Constant(s1.clone())
                } else {
                    StringConst::Top
                }
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringConst::Bottom, _) | (_, StringConst::Bottom) => StringConst::Bottom,
            (StringConst::Top, e) | (e, StringConst::Top) => e.clone(),
            (StringConst::Constant(s1), StringConst::Constant(s2)) => {
                if s1 == s2 {
                    StringConst::Constant(s1.clone())
                } else {
                    StringConst::Bottom
                }
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // For flat lattice, widening is same as join
        self.join(elem1, elem2)
    }
}

/// String Length Domain.
///
/// Abstracts strings by their length using the Interval Domain.
/// Maps string variables to intervals representing their possible lengths.
#[derive(Clone, Debug)]
pub struct StringLengthDomain {
    interval_domain: IntervalDomain,
}

impl StringLengthDomain {
    /// Create a length domain backed by the interval domain.
    ///
    /// Each string variable `s` is represented by an interval for `len(s)`.
    pub fn new() -> Self {
        Self {
            interval_domain: IntervalDomain,
        }
    }

    /// Get the length interval for a variable.
    pub fn get_length(&self, elem: &IntervalElement, var: &str) -> Interval {
        elem.get(var)
    }

    /// Assign a string constant: s = "abc" => len(s) = 3
    pub fn assign_const(&self, elem: &IntervalElement, var: &str, value: &str) -> IntervalElement {
        let len = value.len() as i64;
        self.interval_domain.assign(elem, &var.to_string(), &NumExpr::constant(len))
    }

    /// Assign concatenation: s = s1 + s2 => len(s) = len(s1) + len(s2)
    pub fn assign_concat(&self, elem: &IntervalElement, var: &str, s1: &str, s2: &str) -> IntervalElement {
        let expr = NumExpr::var(s1.to_string()).add(NumExpr::var(s2.to_string()));
        self.interval_domain.assign(elem, &var.to_string(), &expr)
    }

    /// Assume a constraint on the length of a string variable.
    pub fn assume_length(&self, elem: &IntervalElement, pred: &NumPred<String, i64>) -> IntervalElement {
        self.interval_domain.assume(elem, pred)
    }
}

impl Default for StringLengthDomain {
    fn default() -> Self {
        Self::new()
    }
}

impl AbstractDomain for StringLengthDomain {
    type Element = IntervalElement;

    fn bottom(&self) -> Self::Element {
        self.interval_domain.bottom()
    }

    fn top(&self) -> Self::Element {
        self.interval_domain.top()
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        self.interval_domain.is_bottom(elem)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        self.interval_domain.is_top(elem)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        self.interval_domain.le(elem1, elem2)
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.interval_domain.join(elem1, elem2)
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.interval_domain.meet(elem1, elem2)
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.interval_domain.widen(elem1, elem2)
    }
}

/// String Prefix Domain.
///
/// Tracks the known prefix of a string.
/// Useful for checking if a string starts with a specific sequence (e.g. "https://").
///
/// Lattice:
/// - `⊥ ⊑ Prefix(s) ⊑ Prefix("")` (Top)
/// - `Prefix(long) ⊑ Prefix(short)` if `short` is prefix of `long`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringPrefix {
    Bottom,
    Prefix(String),
}

#[derive(Clone, Debug)]
pub struct StringPrefixDomain;

impl StringPrefixDomain {
    /// Concatenate two abstract string prefixes.
    /// concat(Prefix(p1), Prefix(p2)) = Prefix(p1)
    /// Because s1 starts with p1, s1 + s2 also starts with p1.
    pub fn concat(&self, elem1: &StringPrefix, elem2: &StringPrefix) -> StringPrefix {
        match (elem1, elem2) {
            (StringPrefix::Bottom, _) | (_, StringPrefix::Bottom) => StringPrefix::Bottom,
            (StringPrefix::Prefix(p1), _) => StringPrefix::Prefix(p1.clone()),
        }
    }
}

impl AbstractDomain for StringPrefixDomain {
    type Element = StringPrefix;

    fn bottom(&self) -> Self::Element {
        StringPrefix::Bottom
    }

    fn top(&self) -> Self::Element {
        StringPrefix::Prefix(String::new())
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringPrefix::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringPrefix::Prefix(s) if s.is_empty())
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringPrefix::Bottom, _) => true,
            (_, StringPrefix::Bottom) => false,
            (_, StringPrefix::Prefix(s2)) if s2.is_empty() => true, // s2 is Top
            (StringPrefix::Prefix(s1), StringPrefix::Prefix(s2)) => s1.starts_with(s2),
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringPrefix::Bottom, e) | (e, StringPrefix::Bottom) => e.clone(),
            (StringPrefix::Prefix(s1), StringPrefix::Prefix(s2)) => {
                // Longest common prefix
                let lcp: String = s1.chars().zip(s2.chars()).take_while(|(c1, c2)| c1 == c2).map(|(c, _)| c).collect();
                StringPrefix::Prefix(lcp)
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringPrefix::Bottom, _) | (_, StringPrefix::Bottom) => StringPrefix::Bottom,
            (StringPrefix::Prefix(s1), StringPrefix::Prefix(s2)) => {
                if s1.starts_with(s2) {
                    StringPrefix::Prefix(s1.clone())
                } else if s2.starts_with(s1) {
                    StringPrefix::Prefix(s2.clone())
                } else {
                    StringPrefix::Bottom // Incompatible prefixes
                }
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // Prefix length decreases (or stays same) in join, so it has finite height
        // (bounded by 0). No special widening needed.
        self.join(elem1, elem2)
    }
}

/// Character Set Domain.
///
/// Tracks the set of characters that MAY appear in the string.
/// Useful for validation (e.g. ensuring only digits are present).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CharacterSet {
    Bottom,              // No value
    Set(BTreeSet<char>), // Subset of characters
    Top,                 // Any character
}

#[derive(Clone, Debug)]
pub struct CharacterSetDomain;

impl CharacterSetDomain {
    /// Create a character set from a concrete string.
    /// The set will contain all unique characters in the string.
    pub fn from_string(&self, s: &str) -> CharacterSet {
        let mut set = BTreeSet::new();
        for c in s.chars() {
            set.insert(c);
        }
        CharacterSet::Set(set)
    }

    /// Concatenate two character sets.
    /// The result contains the union of characters from both sets.
    pub fn concat(&self, elem1: &CharacterSet, elem2: &CharacterSet) -> CharacterSet {
        match (elem1, elem2) {
            (CharacterSet::Bottom, _) | (_, CharacterSet::Bottom) => CharacterSet::Bottom,
            (CharacterSet::Top, _) | (_, CharacterSet::Top) => CharacterSet::Top,
            (CharacterSet::Set(s1), CharacterSet::Set(s2)) => {
                let mut res = s1.clone();
                res.extend(s2.iter().cloned());
                CharacterSet::Set(res)
            }
        }
    }
}

impl AbstractDomain for CharacterSetDomain {
    type Element = CharacterSet;

    fn bottom(&self) -> Self::Element {
        CharacterSet::Bottom
    }

    fn top(&self) -> Self::Element {
        CharacterSet::Top
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, CharacterSet::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, CharacterSet::Top)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (CharacterSet::Bottom, _) => true,
            (_, CharacterSet::Top) => true,
            (CharacterSet::Set(s1), CharacterSet::Set(s2)) => s1.is_subset(s2),
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (CharacterSet::Bottom, e) | (e, CharacterSet::Bottom) => e.clone(),
            (CharacterSet::Top, _) | (_, CharacterSet::Top) => CharacterSet::Top,
            (CharacterSet::Set(s1), CharacterSet::Set(s2)) => {
                let mut res = s1.clone();
                res.extend(s2.iter().cloned());
                CharacterSet::Set(res)
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (CharacterSet::Bottom, _) | (_, CharacterSet::Bottom) => CharacterSet::Bottom,
            (CharacterSet::Top, e) | (e, CharacterSet::Top) => e.clone(),
            (CharacterSet::Set(s1), CharacterSet::Set(s2)) => {
                let res: BTreeSet<char> = s1.intersection(s2).cloned().collect();
                CharacterSet::Set(res)
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // Character set can grow, but is bounded by alphabet size (finite).
        // However, full unicode is large.
        // For safety, we could widen to Top if size exceeds a threshold.
        // For now, just join.
        self.join(elem1, elem2)
    }
}

/// String Suffix Domain.
///
/// Tracks the known suffix of a string.
/// Useful for checking file extensions or specific endings.
///
/// Lattice:
/// - `⊥ ⊑ Suffix(s) ⊑ Suffix("")` (Top)
/// - `Suffix(long) ⊑ Suffix(short)` if `short` is suffix of `long`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringSuffix {
    Bottom,
    Suffix(String),
}

#[derive(Clone, Debug)]
pub struct StringSuffixDomain;

impl StringSuffixDomain {
    /// Concatenate two abstract string suffixes.
    /// concat(Suffix(s1), Suffix(s2)) = Suffix(s2)
    /// The suffix of the result is determined by the second part.
    pub fn concat(&self, elem1: &StringSuffix, elem2: &StringSuffix) -> StringSuffix {
        match (elem1, elem2) {
            (StringSuffix::Bottom, _) | (_, StringSuffix::Bottom) => StringSuffix::Bottom,
            (_, StringSuffix::Suffix(s2)) => StringSuffix::Suffix(s2.clone()),
        }
    }
}

impl AbstractDomain for StringSuffixDomain {
    type Element = StringSuffix;

    fn bottom(&self) -> Self::Element {
        StringSuffix::Bottom
    }

    fn top(&self) -> Self::Element {
        StringSuffix::Suffix(String::new())
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringSuffix::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringSuffix::Suffix(s) if s.is_empty())
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringSuffix::Bottom, _) => true,
            (_, StringSuffix::Bottom) => false,
            (_, StringSuffix::Suffix(s2)) if s2.is_empty() => true, // s2 is Top
            (StringSuffix::Suffix(s1), StringSuffix::Suffix(s2)) => s1.ends_with(s2),
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringSuffix::Bottom, e) | (e, StringSuffix::Bottom) => e.clone(),
            (StringSuffix::Suffix(s1), StringSuffix::Suffix(s2)) => {
                // Longest common suffix
                let s1_rev: String = s1.chars().rev().collect();
                let s2_rev: String = s2.chars().rev().collect();
                let lcs_rev: String = s1_rev
                    .chars()
                    .zip(s2_rev.chars())
                    .take_while(|(c1, c2)| c1 == c2)
                    .map(|(c, _)| c)
                    .collect();
                let lcs: String = lcs_rev.chars().rev().collect();
                StringSuffix::Suffix(lcs)
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringSuffix::Bottom, _) | (_, StringSuffix::Bottom) => StringSuffix::Bottom,
            (StringSuffix::Suffix(s1), StringSuffix::Suffix(s2)) => {
                if s1.ends_with(s2) {
                    StringSuffix::Suffix(s1.clone())
                } else if s2.ends_with(s1) {
                    StringSuffix::Suffix(s2.clone())
                } else {
                    StringSuffix::Bottom // Incompatible suffixes
                }
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

/// String Inclusion Domain.
///
/// Tracks a set of substrings that MUST be present in the string.
///
/// Lattice:
/// - `⊥ ⊑ Included(Set) ⊑ Included({})` (Top)
/// - `Included(A) ⊑ Included(B)` if `B ⊆ A`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringInclusion {
    Bottom,
    Included(BTreeSet<String>),
}

#[derive(Clone, Debug)]
pub struct StringInclusionDomain;

impl StringInclusionDomain {
    /// Create an inclusion set from a concrete string.
    /// The set will contain the string itself as a required substring.
    pub fn from_string(&self, s: &str) -> StringInclusion {
        let mut set = BTreeSet::new();
        set.insert(s.to_string());
        StringInclusion::Included(set)
    }

    /// Concatenate two inclusion sets.
    /// The result requires all substrings from both operands.
    pub fn concat(&self, elem1: &StringInclusion, elem2: &StringInclusion) -> StringInclusion {
        match (elem1, elem2) {
            (StringInclusion::Bottom, _) | (_, StringInclusion::Bottom) => StringInclusion::Bottom,
            (StringInclusion::Included(s1), StringInclusion::Included(s2)) => {
                let mut res = s1.clone();
                res.extend(s2.iter().cloned());
                StringInclusion::Included(res)
            }
        }
    }
}

impl AbstractDomain for StringInclusionDomain {
    type Element = StringInclusion;

    fn bottom(&self) -> Self::Element {
        StringInclusion::Bottom
    }

    fn top(&self) -> Self::Element {
        StringInclusion::Included(BTreeSet::new())
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringInclusion::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringInclusion::Included(s) if s.is_empty())
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringInclusion::Bottom, _) => true,
            (_, StringInclusion::Bottom) => false,
            (StringInclusion::Included(s1), StringInclusion::Included(s2)) => s2.is_subset(s1),
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringInclusion::Bottom, e) | (e, StringInclusion::Bottom) => e.clone(),
            (StringInclusion::Included(s1), StringInclusion::Included(s2)) => {
                // Intersection: only keep substrings present in BOTH paths
                let res: BTreeSet<String> = s1.intersection(s2).cloned().collect();
                StringInclusion::Included(res)
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringInclusion::Bottom, _) | (_, StringInclusion::Bottom) => StringInclusion::Bottom,
            (StringInclusion::Included(s1), StringInclusion::Included(s2)) => {
                // Union: result must contain everything from both
                let mut res = s1.clone();
                res.extend(s2.iter().cloned());
                StringInclusion::Included(res)
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

/// Taint Analysis Domain.
///
/// Tracks whether a string is "tainted" (from untrusted input) or "safe".
///
/// Lattice:
/// - `⊥ ⊑ Safe ⊑ Tainted` (Top)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Taint {
    Bottom,
    Safe,
    Tainted,
}

#[derive(Clone, Debug)]
pub struct TaintDomain;

impl TaintDomain {
    /// Mark a value as tainted (e.g. from user input).
    pub fn taint(&self) -> Taint {
        Taint::Tainted
    }

    /// Mark a value as safe (e.g. after sanitization).
    pub fn sanitize(&self) -> Taint {
        Taint::Safe
    }

    /// Concatenate taint values.
    /// If any part is tainted, the result is tainted.
    pub fn concat(&self, elem1: &Taint, elem2: &Taint) -> Taint {
        match (elem1, elem2) {
            (Taint::Bottom, _) | (_, Taint::Bottom) => Taint::Bottom,
            (Taint::Tainted, _) | (_, Taint::Tainted) => Taint::Tainted,
            (Taint::Safe, Taint::Safe) => Taint::Safe,
        }
    }
}

impl AbstractDomain for TaintDomain {
    type Element = Taint;

    fn bottom(&self) -> Self::Element {
        Taint::Bottom
    }

    fn top(&self) -> Self::Element {
        Taint::Tainted
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, Taint::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, Taint::Tainted)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (Taint::Bottom, _) => true,
            (_, Taint::Tainted) => true,
            (Taint::Safe, Taint::Safe) => true,
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (Taint::Bottom, e) | (e, Taint::Bottom) => e.clone(),
            (Taint::Tainted, _) | (_, Taint::Tainted) => Taint::Tainted,
            (Taint::Safe, Taint::Safe) => Taint::Safe,
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (Taint::Bottom, _) | (_, Taint::Bottom) => Taint::Bottom,
            (Taint::Tainted, e) | (e, Taint::Tainted) => e.clone(),
            (Taint::Safe, Taint::Safe) => Taint::Safe,
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

/// String Case Domain.
///
/// Tracks the casing of characters in the string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringCase {
    Bottom,
    Lowercase, // Only lowercase or non-cased
    Uppercase, // Only uppercase or non-cased
    Mixed,     // Both or unknown (Top)
}

#[derive(Clone, Debug)]
pub struct StringCaseDomain;

impl StringCaseDomain {
    /// Abstract a concrete string into its casing class.
    ///
    /// This is a helper for building initial states from literals.
    pub fn from_string(&self, s: &str) -> StringCase {
        let has_upper = s.chars().any(|c| c.is_uppercase());
        let has_lower = s.chars().any(|c| c.is_lowercase());

        match (has_upper, has_lower) {
            (false, false) => StringCase::Lowercase, // e.g. "123", treat as lower (or upper)
            (false, true) => StringCase::Lowercase,
            (true, false) => StringCase::Uppercase,
            (true, true) => StringCase::Mixed,
        }
    }

    /// Model `toUpperCase`.
    ///
    /// This is intentionally coarse: any non-bottom input maps to `Uppercase`.
    pub fn to_upper(&self, _elem: &StringCase) -> StringCase {
        StringCase::Uppercase
    }

    /// Model `toLowerCase`.
    ///
    /// This is intentionally coarse: any non-bottom input maps to `Lowercase`.
    pub fn to_lower(&self, _elem: &StringCase) -> StringCase {
        StringCase::Lowercase
    }

    /// Approximate concatenation.
    ///
    /// If either side is `Mixed`, the result is `Mixed`.
    /// Otherwise it stays `Lowercase`/`Uppercase` when both sides agree.
    pub fn concat(&self, elem1: &StringCase, elem2: &StringCase) -> StringCase {
        match (elem1, elem2) {
            (StringCase::Bottom, _) | (_, StringCase::Bottom) => StringCase::Bottom,
            (StringCase::Mixed, _) | (_, StringCase::Mixed) => StringCase::Mixed,
            (StringCase::Lowercase, StringCase::Lowercase) => StringCase::Lowercase,
            (StringCase::Uppercase, StringCase::Uppercase) => StringCase::Uppercase,
            _ => StringCase::Mixed,
        }
    }
}

impl AbstractDomain for StringCaseDomain {
    type Element = StringCase;

    fn bottom(&self) -> Self::Element {
        StringCase::Bottom
    }

    fn top(&self) -> Self::Element {
        StringCase::Mixed
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringCase::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringCase::Mixed)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringCase::Bottom, _) => true,
            (_, StringCase::Mixed) => true,
            (StringCase::Lowercase, StringCase::Lowercase) => true,
            (StringCase::Uppercase, StringCase::Uppercase) => true,
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringCase::Bottom, e) | (e, StringCase::Bottom) => e.clone(),
            (StringCase::Mixed, _) | (_, StringCase::Mixed) => StringCase::Mixed,
            (StringCase::Lowercase, StringCase::Lowercase) => StringCase::Lowercase,
            (StringCase::Uppercase, StringCase::Uppercase) => StringCase::Uppercase,
            _ => StringCase::Mixed,
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringCase::Bottom, _) | (_, StringCase::Bottom) => StringCase::Bottom,
            (StringCase::Mixed, e) | (e, StringCase::Mixed) => e.clone(),
            (StringCase::Lowercase, StringCase::Lowercase) => StringCase::Lowercase,
            (StringCase::Uppercase, StringCase::Uppercase) => StringCase::Uppercase,
            _ => StringCase::Bottom, // Incompatible
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

/// String Numeric Domain.
///
/// Tracks if a string is a valid number representation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringNumeric {
    Bottom,
    IntegerStr, // Valid integer
    FloatStr,   // Valid float (includes integers)
    Top,        // Unknown (could be number or not)
}

#[derive(Clone, Debug)]
pub struct StringNumericDomain;

impl StringNumericDomain {
    /// Classify a concrete string literal by numeric parsability.
    ///
    /// - integers map to `IntegerStr`,
    /// - other floats map to `FloatStr`,
    /// - non-numbers map to `Top` (unknown / not a number).
    pub fn from_string(&self, s: &str) -> StringNumeric {
        if s.parse::<i64>().is_ok() {
            StringNumeric::IntegerStr
        } else if s.parse::<f64>().is_ok() {
            StringNumeric::FloatStr
        } else {
            StringNumeric::Top
        }
    }

    /// Approximate concatenation.
    ///
    /// Concatenating two numeric strings does not reliably yield a numeric string
    /// (e.g. `"-1" + "-2" = "-1-2"`). This implementation is conservative.
    pub fn concat(&self, elem1: &StringNumeric, elem2: &StringNumeric) -> StringNumeric {
        match (elem1, elem2) {
            (StringNumeric::Bottom, _) | (_, StringNumeric::Bottom) => StringNumeric::Bottom,
            (StringNumeric::IntegerStr, StringNumeric::IntegerStr) => {
                // "1" + "2" = "12" (Integer)
                // But "-1" + "-2" = "-1-2" (Not number)
                // For simplicity, assume Top unless we check signs.
                StringNumeric::Top
            }
            _ => StringNumeric::Top,
        }
    }
}

impl AbstractDomain for StringNumericDomain {
    type Element = StringNumeric;

    fn bottom(&self) -> Self::Element {
        StringNumeric::Bottom
    }

    fn top(&self) -> Self::Element {
        StringNumeric::Top
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringNumeric::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringNumeric::Top)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringNumeric::Bottom, _) => true,
            (_, StringNumeric::Top) => true,
            (StringNumeric::IntegerStr, StringNumeric::IntegerStr) => true,
            (StringNumeric::FloatStr, StringNumeric::FloatStr) => true,
            (StringNumeric::IntegerStr, StringNumeric::FloatStr) => true, // Int is subset of Float
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringNumeric::Bottom, e) | (e, StringNumeric::Bottom) => e.clone(),
            (StringNumeric::Top, _) | (_, StringNumeric::Top) => StringNumeric::Top,
            (StringNumeric::IntegerStr, StringNumeric::IntegerStr) => StringNumeric::IntegerStr,
            (StringNumeric::FloatStr, StringNumeric::FloatStr) => StringNumeric::FloatStr,
            (StringNumeric::IntegerStr, StringNumeric::FloatStr) | (StringNumeric::FloatStr, StringNumeric::IntegerStr) => {
                StringNumeric::FloatStr
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringNumeric::Bottom, _) | (_, StringNumeric::Bottom) => StringNumeric::Bottom,
            (StringNumeric::Top, e) | (e, StringNumeric::Top) => e.clone(),
            (StringNumeric::IntegerStr, StringNumeric::IntegerStr) => StringNumeric::IntegerStr,
            (StringNumeric::FloatStr, StringNumeric::FloatStr) => StringNumeric::FloatStr,
            (StringNumeric::IntegerStr, StringNumeric::FloatStr) | (StringNumeric::FloatStr, StringNumeric::IntegerStr) => {
                StringNumeric::IntegerStr
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        self.join(elem1, elem2)
    }
}

/// Regex Domain.
///
/// Tracks the structure of strings using Regular Expressions.
///
/// Lattice:
/// - `⊥ ⊑ Regex(r) ⊑ ⊤` (.*)
///
/// Note: This domain uses syntactic equality for ordering to avoid
/// the high complexity of checking regex inclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringRegex {
    Bottom,
    Regex(String),
    Top,
}

#[derive(Clone, Debug)]
pub struct RegexDomain {
    /// Maximum length of regex string before widening to Top.
    /// Prevents infinite growth in loops.
    pub max_length: usize,
}

impl RegexDomain {
    /// Create a regex domain with a maximum pattern size.
    ///
    /// Concatenation widens to `Top` once the syntactic regex grows beyond `max_length`.
    pub fn new(max_length: usize) -> Self {
        Self { max_length }
    }

    /// Create a regex from a constant string.
    /// Escapes special regex characters.
    pub fn from_string(&self, s: &str) -> StringRegex {
        // Simple regex escaping
        let escaped = s
            .replace('\\', "\\\\")
            .replace('.', "\\.")
            .replace('+', "\\+")
            .replace('*', "\\*")
            .replace('?', "\\?")
            .replace('(', "\\(")
            .replace(')', "\\)")
            .replace('[', "\\[")
            .replace(']', "\\]")
            .replace('{', "\\{")
            .replace('}', "\\}")
            .replace('|', "\\|")
            .replace('^', "\\^")
            .replace('$', "\\$");
        StringRegex::Regex(escaped)
    }

    /// Create a regex from a raw pattern (assumed valid).
    pub fn from_pattern(&self, p: &str) -> StringRegex {
        StringRegex::Regex(p.to_string())
    }

    /// Concatenate two regexes.
    /// r1 + r2 -> r1r2
    pub fn concat(&self, elem1: &StringRegex, elem2: &StringRegex) -> StringRegex {
        match (elem1, elem2) {
            (StringRegex::Bottom, _) | (_, StringRegex::Bottom) => StringRegex::Bottom,
            (StringRegex::Top, _) | (_, StringRegex::Top) => StringRegex::Top,
            (StringRegex::Regex(r1), StringRegex::Regex(r2)) => {
                // Wrap in parentheses if the regex contains alternation '|'
                // to preserve precedence.
                // Conservative check: if it contains '|', wrap it.
                // (Even if escaped '\|', wrapping is safe).
                let p1 = if r1.contains('|') { format!("({})", r1) } else { r1.clone() };
                let p2 = if r2.contains('|') { format!("({})", r2) } else { r2.clone() };

                let new_regex = format!("{}{}", p1, p2);
                if new_regex.len() > self.max_length {
                    StringRegex::Top
                } else {
                    StringRegex::Regex(new_regex)
                }
            }
        }
    }
}

impl Default for RegexDomain {
    fn default() -> Self {
        Self::new(100)
    }
}

impl AbstractDomain for RegexDomain {
    type Element = StringRegex;

    fn bottom(&self) -> Self::Element {
        StringRegex::Bottom
    }

    fn top(&self) -> Self::Element {
        StringRegex::Top
    }

    fn is_bottom(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringRegex::Bottom)
    }

    fn is_top(&self, elem: &Self::Element) -> bool {
        matches!(elem, StringRegex::Top)
    }

    fn le(&self, elem1: &Self::Element, elem2: &Self::Element) -> bool {
        match (elem1, elem2) {
            (StringRegex::Bottom, _) => true,
            (_, StringRegex::Top) => true,
            (StringRegex::Regex(r1), StringRegex::Regex(r2)) => {
                if r1 == r2 {
                    return true;
                }
                // Check if all components of r1 are in r2
                // This assumes top-level alternation is used for join
                let parts1: Vec<&str> = r1.split('|').collect();
                let parts2: Vec<&str> = r2.split('|').collect();

                parts1.iter().all(|p1| parts2.contains(p1))
            }
            _ => false,
        }
    }

    fn join(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringRegex::Bottom, e) | (e, StringRegex::Bottom) => e.clone(),
            (StringRegex::Top, _) | (_, StringRegex::Top) => StringRegex::Top,
            (StringRegex::Regex(r1), StringRegex::Regex(r2)) => {
                if r1 == r2 {
                    StringRegex::Regex(r1.clone())
                } else {
                    // Union: r1|r2
                    // No need to wrap in parentheses for join itself,
                    // as '|' has lowest precedence.
                    let new_regex = format!("{}|{}", r1, r2);
                    if new_regex.len() > self.max_length {
                        StringRegex::Top
                    } else {
                        StringRegex::Regex(new_regex)
                    }
                }
            }
        }
    }

    fn meet(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        match (elem1, elem2) {
            (StringRegex::Bottom, _) | (_, StringRegex::Bottom) => StringRegex::Bottom,
            (StringRegex::Top, e) | (e, StringRegex::Top) => e.clone(),
            (StringRegex::Regex(r1), StringRegex::Regex(r2)) => {
                if r1 == r2 {
                    StringRegex::Regex(r1.clone())
                } else {
                    // Intersection of regexes is hard.
                    // Conservative approximation: Bottom (assuming they are disjoint)
                    // OR we could return one if we knew inclusion.
                    // For now, return Bottom unless equal.
                    StringRegex::Bottom
                }
            }
        }
    }

    fn widen(&self, elem1: &Self::Element, elem2: &Self::Element) -> Self::Element {
        // Widen uses the same logic as join (union), but checks length limit.
        // Since join already checks length limit, we can just delegate.
        self.join(elem1, elem2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::tests::test_lattice_axioms;

    #[test]
    fn test_string_constant_lattice() {
        let domain = StringConstantDomain;
        let samples = vec![
            StringConst::Bottom,
            StringConst::Top,
            StringConst::Constant("hello".to_string()),
            StringConst::Constant("world".to_string()),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_constant_ops() {
        let domain = StringConstantDomain;
        let s1 = StringConst::Constant("foo".to_string());
        let s2 = StringConst::Constant("foo".to_string());
        let s3 = StringConst::Constant("bar".to_string());

        assert!(domain.le(&s1, &s2));
        assert!(!domain.le(&s1, &s3));
        assert_eq!(domain.join(&s1, &s3), StringConst::Top);
        assert_eq!(domain.meet(&s1, &s3), StringConst::Bottom);
    }

    #[test]
    fn test_string_length_domain() {
        let domain = StringLengthDomain::new();
        let mut state = domain.top();

        // s1 = "hello" (len 5)
        state = domain.assign_const(&state, "s1", "hello");
        let len_s1 = domain.get_length(&state, "s1");
        assert_eq!(len_s1, Interval::constant(5));

        // s2 = "world" (len 5)
        state = domain.assign_const(&state, "s2", "world");

        // s3 = s1 + s2 (len 10)
        state = domain.assign_concat(&state, "s3", "s1", "s2");
        let len_s3 = domain.get_length(&state, "s3");
        assert_eq!(len_s3, Interval::constant(10));
    }

    #[test]
    fn test_string_prefix_domain() {
        let domain = StringPrefixDomain;
        let p1 = StringPrefix::Prefix("hello".to_string());
        let p2 = StringPrefix::Prefix("help".to_string());
        let p3 = StringPrefix::Prefix("he".to_string());

        // Order: "hello" <= "he" (because "hello" starts with "he")
        assert!(domain.le(&p1, &p3));
        assert!(!domain.le(&p3, &p1));

        // Join: LCP("hello", "help") = "hel"
        let joined = domain.join(&p1, &p2);
        assert_eq!(joined, StringPrefix::Prefix("hel".to_string()));

        // Meet: "hello" ⊓ "he" = "hello"
        let meet = domain.meet(&p1, &p3);
        assert_eq!(meet, p1);

        // Concat: "hello" + "world" -> starts with "hello"
        let concat = domain.concat(&p1, &StringPrefix::Prefix("world".to_string()));
        assert_eq!(concat, p1);
    }

    #[test]
    fn test_character_set_domain() {
        let domain = CharacterSetDomain;
        let s1 = domain.from_string("abc");
        let s2 = domain.from_string("bcd");

        // Join: {a,b,c} ⊔ {b,c,d} = {a,b,c,d}
        let joined = domain.join(&s1, &s2);
        if let CharacterSet::Set(set) = joined {
            assert_eq!(set.len(), 4);
            assert!(set.contains(&'a'));
            assert!(set.contains(&'d'));
        } else {
            panic!("Expected Set");
        }

        // Meet: {a,b,c} ⊓ {b,c,d} = {b,c}
        let meet = domain.meet(&s1, &s2);
        if let CharacterSet::Set(set) = meet {
            assert_eq!(set.len(), 2);
            assert!(set.contains(&'b'));
            assert!(set.contains(&'c'));
            assert!(!set.contains(&'a'));
        } else {
            panic!("Expected Set");
        }
    }

    #[test]
    fn test_string_suffix_domain() {
        let domain = StringSuffixDomain;
        let s1 = StringSuffix::Suffix("file.txt".to_string());
        let s2 = StringSuffix::Suffix("image.txt".to_string());
        let s3 = StringSuffix::Suffix(".txt".to_string());

        // Order: "file.txt" <= ".txt"
        assert!(domain.le(&s1, &s3));
        assert!(!domain.le(&s3, &s1));

        // Join: LCSuf("file.txt", "image.txt") = "e.txt"
        let joined = domain.join(&s1, &s2);
        assert_eq!(joined, StringSuffix::Suffix("e.txt".to_string()));

        // Concat: "path/" + "file.txt" -> ends with "file.txt"
        let prefix = StringSuffix::Suffix("path/".to_string());
        let concat = domain.concat(&prefix, &s1);
        assert_eq!(concat, s1);
    }

    #[test]
    fn test_string_inclusion_domain() {
        let domain = StringInclusionDomain;
        let i1 = domain.from_string("foo");
        let i2 = domain.from_string("bar");

        // Concat: must contain "foo" AND "bar"
        let concat = domain.concat(&i1, &i2);
        if let StringInclusion::Included(set) = &concat {
            assert!(set.contains("foo"));
            assert!(set.contains("bar"));
        } else {
            panic!("Expected Included");
        }

        // Join: path1 has {foo, bar}, path2 has {foo} -> result {foo}
        let i3 = domain.from_string("foo");
        let joined = domain.join(&concat, &i3);
        if let StringInclusion::Included(set) = &joined {
            assert!(set.contains("foo"));
            assert!(!set.contains("bar"));
        } else {
            panic!("Expected Included");
        }
    }

    #[test]
    fn test_taint_domain() {
        let domain = TaintDomain;
        let safe = Taint::Safe;
        let tainted = Taint::Tainted;

        // Order: Safe <= Tainted
        assert!(domain.le(&safe, &tainted));
        assert!(!domain.le(&tainted, &safe));

        // Join: Safe ⊔ Tainted = Tainted
        assert_eq!(domain.join(&safe, &tainted), Taint::Tainted);

        // Concat: Safe + Safe = Safe
        assert_eq!(domain.concat(&safe, &safe), Taint::Safe);
        // Concat: Safe + Tainted = Tainted
        assert_eq!(domain.concat(&safe, &tainted), Taint::Tainted);
    }

    #[test]
    fn test_string_case_domain() {
        let domain = StringCaseDomain;
        let lower = StringCase::Lowercase;
        let upper = StringCase::Uppercase;
        let mixed = StringCase::Mixed;

        // Order: Lower <= Mixed, Upper <= Mixed
        assert!(domain.le(&lower, &mixed));
        assert!(domain.le(&upper, &mixed));
        // Lower and Upper are incomparable
        assert!(!domain.le(&lower, &upper));
        assert!(!domain.le(&upper, &lower));

        // Join: Lower ⊔ Upper = Mixed
        assert_eq!(domain.join(&lower, &upper), StringCase::Mixed);

        // From string
        assert_eq!(domain.from_string("abc"), StringCase::Lowercase);
        assert_eq!(domain.from_string("ABC"), StringCase::Uppercase);
        assert_eq!(domain.from_string("aBc"), StringCase::Mixed);
        assert_eq!(domain.from_string("123"), StringCase::Lowercase); // Treated as lower (no upper chars)
    }

    #[test]
    fn test_string_numeric_domain() {
        let domain = StringNumericDomain;
        let int_str = StringNumeric::IntegerStr;
        let float_str = StringNumeric::FloatStr;
        let top = StringNumeric::Top;

        // Order: Int <= Float <= Top
        assert!(domain.le(&int_str, &float_str));
        assert!(domain.le(&float_str, &top));

        // Join: Int ⊔ Float = Float
        assert_eq!(domain.join(&int_str, &float_str), StringNumeric::FloatStr);

        // From string
        assert_eq!(domain.from_string("123"), StringNumeric::IntegerStr);
        assert_eq!(domain.from_string("-456"), StringNumeric::IntegerStr);
        assert_eq!(domain.from_string("123.45"), StringNumeric::FloatStr);
        assert_eq!(domain.from_string("abc"), StringNumeric::Top);
    }

    #[test]
    fn test_regex_domain() {
        let domain = RegexDomain::default();
        let r1 = domain.from_string("abc");
        let r2 = domain.from_string("def");
        let top = StringRegex::Top;

        // Order
        assert!(domain.le(&r1, &r1));
        assert!(!domain.le(&r1, &r2));
        assert!(domain.le(&r1, &top));

        // Concat: "abc" + "def" -> "abcdef"
        let concat = domain.concat(&r1, &r2);
        if let StringRegex::Regex(s) = concat {
            assert_eq!(s, "abcdef");
        } else {
            panic!("Expected Regex");
        }

        // Join: "abc" | "def" -> "abc|def"
        let joined = domain.join(&r1, &r2);
        if let StringRegex::Regex(s) = joined {
            assert_eq!(s, "abc|def");
        } else {
            panic!("Expected Regex");
        }

        // Widen (Length limit)
        let small_domain = RegexDomain::new(10); // Very small limit
        let long_r1 = small_domain.from_string("123456");
        let long_r2 = small_domain.from_string("789012");
        // "123456" + "789012" = 12 chars > 10 -> Top
        let wide_concat = small_domain.concat(&long_r1, &long_r2);
        assert_eq!(wide_concat, StringRegex::Top);
    }

    #[test]
    fn test_string_length_lattice_axioms() {
        let domain = StringLengthDomain::new();
        let samples = vec![
            domain.bottom(),
            domain.top(),
            domain.assign_const(&domain.top(), "s", "hello"),
            domain.assign_const(&domain.top(), "s", ""),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_prefix_lattice_axioms() {
        let domain = StringPrefixDomain;
        let samples = vec![
            StringPrefix::Bottom,
            StringPrefix::Prefix(String::new()),
            StringPrefix::Prefix("a".to_string()),
            StringPrefix::Prefix("ab".to_string()),
            StringPrefix::Prefix("b".to_string()),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_character_set_lattice_axioms() {
        let domain = CharacterSetDomain;
        let samples = vec![
            CharacterSet::Bottom,
            CharacterSet::Top,
            domain.from_string("a"),
            domain.from_string("ab"),
            domain.from_string("b"),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_suffix_lattice_axioms() {
        let domain = StringSuffixDomain;
        let samples = vec![
            StringSuffix::Bottom,
            StringSuffix::Suffix(String::new()),
            StringSuffix::Suffix("a".to_string()),
            StringSuffix::Suffix("ba".to_string()),
            StringSuffix::Suffix("b".to_string()),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_inclusion_lattice_axioms() {
        let domain = StringInclusionDomain;
        let samples = vec![
            StringInclusion::Bottom,
            StringInclusion::Included(BTreeSet::new()),
            domain.from_string("foo"),
            domain.from_string("bar"),
            domain.join(&domain.from_string("foo"), &domain.from_string("bar")),
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_taint_lattice_axioms() {
        let domain = TaintDomain;
        let samples = vec![Taint::Bottom, Taint::Tainted, Taint::Safe];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_case_lattice_axioms() {
        let domain = StringCaseDomain;
        let samples = vec![StringCase::Bottom, StringCase::Mixed, StringCase::Lowercase, StringCase::Uppercase];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_string_numeric_lattice_axioms() {
        let domain = StringNumericDomain;
        let samples = vec![
            StringNumeric::Bottom,
            StringNumeric::Top,
            StringNumeric::IntegerStr,
            StringNumeric::FloatStr,
        ];
        test_lattice_axioms(&domain, &samples);
    }

    #[test]
    fn test_regex_lattice_axioms() {
        let domain = RegexDomain::default();
        let samples = vec![
            StringRegex::Bottom,
            StringRegex::Top,
            domain.from_string("a"),
            domain.from_string("b"),
            domain.join(&domain.from_string("a"), &domain.from_string("b")),
        ];
        test_lattice_axioms(&domain, &samples);
    }
}
