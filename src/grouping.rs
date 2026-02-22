use vstd::prelude::*;

#[allow(unused_imports)]
use crate::doc_item::*;

verus! {

/// Spec-level lexicographic comparison for module path strings.
/// Returns true if `a` is lexicographically less than or equal to `b`.
pub open spec fn module_path_le(a: Seq<char>, b: Seq<char>) -> bool {
    seq_char_le(a, b)
}

/// Reflexivity: a path is always <= itself.
pub proof fn lemma_seq_char_le_reflexive(a: Seq<char>)
    ensures
        seq_char_le(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_seq_char_le_reflexive(a.skip(1));
    }
}

/// Transitivity of seq_char_le.
pub proof fn lemma_seq_char_le_transitive(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        seq_char_le(a, b),
        seq_char_le(b, c),
    ensures
        seq_char_le(a, c),
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 && c.len() > 0 {
        if a[0] == b[0] && b[0] == c[0] {
            lemma_seq_char_le_transitive(a.skip(1), b.skip(1), c.skip(1));
        }
    }
}

/// Antisymmetry: if a <= b and b <= a then they are equal (same length and elements).
pub proof fn lemma_seq_char_le_antisymmetric(a: Seq<char>, b: Seq<char>)
    requires
        seq_char_le(a, b),
        seq_char_le(b, a),
    ensures
        a =~= b,
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 {
        lemma_seq_char_le_antisymmetric(a.skip(1), b.skip(1));
    }
}

/// Totality: for any two sequences, either a <= b or b <= a.
pub proof fn lemma_seq_char_le_total(a: Seq<char>, b: Seq<char>)
    ensures
        seq_char_le(a, b) || seq_char_le(b, a),
    decreases a.len() + b.len(),
{
    if a.len() > 0 && b.len() > 0 {
        if a[0] == b[0] {
            lemma_seq_char_le_total(a.skip(1), b.skip(1));
        }
    }
}

} // verus!
