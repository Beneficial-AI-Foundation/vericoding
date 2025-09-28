// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Kept the helper function `count_truths` as it is correct and useful. */
spec fn count_truths(s: Seq<bool>, predicate: FnSpec<bool, bool>) -> int {
    s.filter(predicate).len() as int
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type mismatches (int vs integer for initial assignment, FnSpec vs concrete closure type), fixed `as_usize()` calls on `int` by casting to `nat` first, and replaced non-existent `subsequence` calls with correct `subslice` calls. Removed `old(a)@.subsequence(i as int, len as int)` from the first loop's multiset invariant as it was incorrectly trying to assert a subsequence of the original array in relation to the current array beyond the modified part. The correct multisets for the second invariant are `a` itself and the multiset created from the rest originally `old(a)@.subslice(...)`. */
{
    let len = a.len();
    let mut false_count: int = 0;
    if len > 0 {
        false_count = count_truths(old(a)@, |x: bool| !x);
    }

    let mut i: usize = 0;
    while i < false_count as nat
        invariant
            0 <= i as int <= len as int,
            a.len() == len,
            a@.subslice(0, i as int).forall(|x: bool| !x),
            a@.to_multiset().add(old(a)@.subslice(i as int, len as int).to_multiset()) == old(a)@.to_multiset(),
    {
        a.set(i, false);
        i = i + 1;
    }

    let mut j: usize = false_count as nat;
    while j < len
        invariant
            0 <= j as int <= len as int,
            a.len() == len,
            a@.subslice(0, false_count as int).forall(|x: bool| !x),
            a@.subslice(false_count as int, j as int).forall(|x: bool| x),
            a@.to_multiset().add(old(a)@.subslice(j as int, len as int).to_multiset()) == old(a)@.to_multiset(),
    {
        a.set(j, true);
        j = j + 1;
    }
}
// </vc-code>

}
fn main() {}