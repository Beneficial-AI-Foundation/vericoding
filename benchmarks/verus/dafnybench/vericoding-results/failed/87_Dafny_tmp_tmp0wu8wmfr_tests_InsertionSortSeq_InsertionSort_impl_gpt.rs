use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
proof fn lemma_sorted_prepend_if_le(x: int, s: Seq<int>)
    requires
        is_sorted(s),
        s.len() == 0 || x <= s[0]
    ensures
        is_sorted(seq![x] + s)
{
    // Prove: for all p<q in seq![x] + s, the order holds
    assert(is_sorted(s));
    assert(forall|p: int, q: int|
        0 <= p < q < (seq![x] + s).len() ==>
        (seq![x] + s)[p] <= (seq![x] + s)[q]
    ) by {
        assert forall|p: int, q: int|
            0 <= p < q < (seq![x] + s).len()
            implies
            (seq![x] + s)[p] <= (seq![x] + s)[q]
        by {
            if p == 0 {
                // q >= 1, relates x and s[q-1]
                assert(1 <= q < (seq![x] + s
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// <vc-code>
proof fn lemma_sorted_prepend_if_le(x: int, s: Seq<int>)
    requires
        is_sorted(s),
        s.len() == 0 || x <= s[0]
    ensures
        is_sorted(seq![x] + s)
{
    // Prove: for all p<q in seq![x] + s, the order holds
    assert(is_sorted(s));
    assert(forall|p: int, q: int|
        0 <= p < q < (seq![x] + s).len() ==>
        (seq![x] + s)[p] <= (seq![x] + s)[q]
    ) by {
        assert forall|p: int, q: int|
            0 <= p < q < (seq![x] + s).len()
            implies
            (seq![x] + s)[p] <= (seq![x] + s)[q]
        by {
            if p == 0 {
                // q >= 1, relates x and s[q-1]
                assert(1 <= q < (seq![x] + s
// </vc-code>

fn main() {}

}