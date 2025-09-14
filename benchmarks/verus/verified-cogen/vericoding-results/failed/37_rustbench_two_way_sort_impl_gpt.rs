// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple boolean sortedness predicate available for reuse */
spec fn is_sorted_bool(s: Seq<bool>) -> bool { forall|i: int, j: int| 0 <= i < j < s.len() ==> !s[i] || s[j] }
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
{
    /* code modified by LLM (iteration 5): use Vec::swap to preserve multiset and maintain partition invariants */
    let n = a.len();
    let mut i: usize = 0;
    let mut j: usize = n;
    while i < j
        invariant
            a.len() == n,
            0 <= i as int <= j as int <= n as int,
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i as int ==> a[k] == false,
            forall|k: int| j as int <= k < n as int ==> a[k] == true
        decreases j as int - i as int
    {
        if !a[i] {
            i += 1;
        } else if a[j - 1] {
            j -= 1;
        } else {
            a.swap(i, j - 1);
            i += 1;
            j -= 1;
        }
    }
}
// </vc-code>

}
fn main() {}