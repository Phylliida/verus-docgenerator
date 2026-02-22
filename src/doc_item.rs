use vstd::prelude::*;

verus! {

/// The kind of a Verus function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FnKind {
    Spec,
    Proof,
    Exec,
}

/// Visibility of a declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    PublicCrate,
    Private,
}

/// Ghost model of a documentation item for verification.
pub struct DocItem {
    pub name: Seq<char>,
    pub kind: FnKind,
    pub visibility: Visibility,
    pub is_open: bool,
    pub line_number: nat,
    pub file_path: Seq<char>,
    pub doc_comment: Option<Seq<char>>,
    pub module_path: Seq<char>,
}

/// Ghost model of a documentation module.
pub struct DocModule {
    pub path: Seq<char>,
    pub items: Seq<DocItem>,
}

/// Ghost model of the full documentation output.
pub struct DocOutput {
    pub modules: Seq<DocModule>,
}

/// Returns the FnKind ordering value for sorting: Spec < Proof < Exec.
pub open spec fn kind_ord(k: FnKind) -> nat {
    match k {
        FnKind::Spec => 0,
        FnKind::Proof => 1,
        FnKind::Exec => 2,
    }
}

/// Items are sorted by line number within a module.
pub open spec fn items_sorted_by_line(items: Seq<DocItem>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < items.len() ==>
            items[i].line_number <= items[j].line_number
}

/// Items are grouped by kind: all Spec, then all Proof, then all Exec.
pub open spec fn items_grouped_by_kind(items: Seq<DocItem>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < items.len() ==>
            kind_ord(items[i].kind) <= kind_ord(items[j].kind)
}

/// All items have Public visibility.
pub open spec fn all_items_public(items: Seq<DocItem>) -> bool {
    forall|i: int| 0 <= i < items.len() ==> items[i].visibility == Visibility::Public
}

/// Modules are sorted alphabetically by path.
pub open spec fn modules_sorted(modules: Seq<DocModule>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < modules.len() ==>
            seq_char_le(modules[i].path, modules[j].path)
}

/// Lexicographic comparison on Seq<char>.
pub open spec fn seq_char_le(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        true
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        (a[0] as nat) < (b[0] as nat)
    } else {
        seq_char_le(a.skip(1), b.skip(1))
    }
}

/// A Seq is a permutation of another if they have the same length
/// and every element in one appears the same number of times in the other.
pub open spec fn is_permutation(a: Seq<DocItem>, b: Seq<DocItem>) -> bool {
    a.len() == b.len()
    && forall|i: int| 0 <= i < a.len() ==>
        exists|j: int| 0 <= j < b.len() && a[i] == b[j]
}

} // verus!

/// Runtime representation of FnKind (mirrors the ghost enum).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RtFnKind {
    Spec,
    Proof,
    Exec,
}

/// Runtime representation of Visibility.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RtVisibility {
    Public,
    PublicCrate,
    Private,
}

/// Runtime documentation item extracted from source.
#[derive(Debug, Clone)]
pub struct RtDocItem {
    pub name: String,
    pub kind: RtFnKind,
    pub visibility: RtVisibility,
    pub is_open: bool,
    pub line_number: usize,
    pub file_path: String,
    pub doc_comment: Option<String>,
    pub module_path: String,
}

/// Runtime documentation module.
#[derive(Debug, Clone)]
pub struct RtDocModule {
    pub path: String,
    pub items: Vec<RtDocItem>,
}

/// Runtime documentation output.
#[derive(Debug, Clone)]
pub struct RtDocOutput {
    pub modules: Vec<RtDocModule>,
}

impl RtFnKind {
    pub fn ord(&self) -> u8 {
        match self {
            RtFnKind::Spec => 0,
            RtFnKind::Proof => 1,
            RtFnKind::Exec => 2,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            RtFnKind::Spec => "spec",
            RtFnKind::Proof => "proof",
            RtFnKind::Exec => "exec",
        }
    }
}

impl RtVisibility {
    pub fn as_str(&self) -> &'static str {
        match self {
            RtVisibility::Public => "pub",
            RtVisibility::PublicCrate => "pub(crate)",
            RtVisibility::Private => "",
        }
    }
}
