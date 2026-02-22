use vstd::prelude::*;
use crate::doc_item::*;

verus! {

/// Filters a sequence to keep only Public items.
/// Proves: all output items are public, output is no longer than input.
pub open spec fn filter_public_spec(items: Seq<DocItem>) -> Seq<DocItem>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_public_spec(items.skip(1));
        if items[0].visibility == Visibility::Public {
            seq![items[0]].add(rest)
        } else {
            rest
        }
    }
}

/// All items in the filtered result are public.
pub proof fn lemma_filter_public_all_public(items: Seq<DocItem>)
    ensures
        all_items_public(filter_public_spec(items)),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_filter_public_all_public(items.skip(1));
    }
}

/// The filtered result is no longer than the input.
pub proof fn lemma_filter_public_length(items: Seq<DocItem>)
    ensures
        filter_public_spec(items).len() <= items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_filter_public_length(items.skip(1));
    }
}

/// Insertion sort by line number (spec).
/// Proves: output is sorted by line number.
pub open spec fn sort_by_line_spec(items: Seq<DocItem>) -> Seq<DocItem>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        insert_sorted_by_line(items[0], sort_by_line_spec(items.skip(1)))
    }
}

/// Insert an item into a line-sorted sequence maintaining sort order.
pub open spec fn insert_sorted_by_line(item: DocItem, sorted: Seq<DocItem>) -> Seq<DocItem>
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        seq![item]
    } else if item.line_number <= sorted[0].line_number {
        seq![item].add(sorted)
    } else {
        seq![sorted[0]].add(insert_sorted_by_line(item, sorted.skip(1)))
    }
}

/// sort_by_line_spec preserves length.
pub proof fn lemma_sort_by_line_length(items: Seq<DocItem>)
    ensures
        sort_by_line_spec(items).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_sort_by_line_length(items.skip(1));
        lemma_insert_sorted_length(items[0], sort_by_line_spec(items.skip(1)));
    }
}

/// insert_sorted_by_line increases length by exactly 1.
pub proof fn lemma_insert_sorted_length(item: DocItem, sorted: Seq<DocItem>)
    ensures
        insert_sorted_by_line(item, sorted).len() == sorted.len() + 1,
    decreases sorted.len(),
{
    if sorted.len() > 0 && item.line_number > sorted[0].line_number {
        lemma_insert_sorted_length(item, sorted.skip(1));
    }
}

/// sort_by_line_spec produces a sorted sequence.
pub proof fn lemma_sort_by_line_sorted(items: Seq<DocItem>)
    ensures
        items_sorted_by_line(sort_by_line_spec(items)),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_sort_by_line_sorted(items.skip(1));
        lemma_insert_preserves_sorted(items[0], sort_by_line_spec(items.skip(1)));
    }
}

/// Inserting into a sorted sequence preserves sort order.
pub proof fn lemma_insert_preserves_sorted(item: DocItem, sorted: Seq<DocItem>)
    requires
        items_sorted_by_line(sorted),
    ensures
        items_sorted_by_line(insert_sorted_by_line(item, sorted)),
    decreases sorted.len(),
{
    if sorted.len() > 0 && item.line_number > sorted[0].line_number {
        lemma_insert_preserves_sorted(item, sorted.skip(1));
    }
}

/// Insertion sort by kind (Spec < Proof < Exec).
pub open spec fn sort_by_kind_spec(items: Seq<DocItem>) -> Seq<DocItem>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        insert_sorted_by_kind(items[0], sort_by_kind_spec(items.skip(1)))
    }
}

/// Insert maintaining kind-grouped order.
pub open spec fn insert_sorted_by_kind(item: DocItem, sorted: Seq<DocItem>) -> Seq<DocItem>
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        seq![item]
    } else if kind_ord(item.kind) <= kind_ord(sorted[0].kind) {
        seq![item].add(sorted)
    } else {
        seq![sorted[0]].add(insert_sorted_by_kind(item, sorted.skip(1)))
    }
}

/// sort_by_kind_spec produces items grouped by kind.
pub proof fn lemma_sort_by_kind_grouped(items: Seq<DocItem>)
    ensures
        items_grouped_by_kind(sort_by_kind_spec(items)),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_sort_by_kind_grouped(items.skip(1));
        lemma_insert_kind_preserves_grouped(items[0], sort_by_kind_spec(items.skip(1)));
    }
}

/// Inserting preserves kind grouping.
pub proof fn lemma_insert_kind_preserves_grouped(item: DocItem, sorted: Seq<DocItem>)
    requires
        items_grouped_by_kind(sorted),
    ensures
        items_grouped_by_kind(insert_sorted_by_kind(item, sorted)),
    decreases sorted.len(),
{
    if sorted.len() > 0 && kind_ord(item.kind) > kind_ord(sorted[0].kind) {
        lemma_insert_kind_preserves_grouped(item, sorted.skip(1));
    }
}

/// sort_by_kind_spec preserves length.
pub proof fn lemma_sort_by_kind_length(items: Seq<DocItem>)
    ensures
        sort_by_kind_spec(items).len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 {
        lemma_sort_by_kind_length(items.skip(1));
        lemma_insert_kind_length(items[0], sort_by_kind_spec(items.skip(1)));
    }
}

/// insert_sorted_by_kind increases length by exactly 1.
pub proof fn lemma_insert_kind_length(item: DocItem, sorted: Seq<DocItem>)
    ensures
        insert_sorted_by_kind(item, sorted).len() == sorted.len() + 1,
    decreases sorted.len(),
{
    if sorted.len() > 0 && kind_ord(item.kind) > kind_ord(sorted[0].kind) {
        lemma_insert_kind_length(item, sorted.skip(1));
    }
}

} // verus!

/// Build the runtime documentation output from a list of public items.
/// Groups by module, sorts modules alphabetically, sorts items by kind within each module.
pub fn build_doc_output(items: Vec<RtDocItem>) -> RtDocOutput {
    use std::collections::BTreeMap;

    // Group items by module path
    let mut modules: BTreeMap<String, Vec<RtDocItem>> = BTreeMap::new();
    for item in items {
        modules.entry(item.module_path.clone()).or_default().push(item);
    }

    // Build sorted modules
    let mut result: Vec<RtDocModule> = Vec::new();
    for (path, mut items) in modules {
        // Sort items: first by kind (spec, proof, exec), then by line number within kind
        items.sort_by(|a, b| {
            a.kind.ord().cmp(&b.kind.ord())
                .then(a.line_number.cmp(&b.line_number))
        });
        result.push(RtDocModule { path, items });
    }

    // BTreeMap already gives us alphabetical module order
    RtDocOutput { modules: result }
}
