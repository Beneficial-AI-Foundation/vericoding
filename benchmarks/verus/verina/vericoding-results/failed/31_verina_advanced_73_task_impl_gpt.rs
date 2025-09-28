// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive spec helper to find first missing nat in a strictly increasing sequence */
spec fn smallest_missing_from(l: Seq<nat>, i: int) -> (result: nat)
    requires
        0 <= i <= l.len(),
        forall|p: int, q: int| 0 <= p < q < l.len() ==> l[p] < l[q],
        forall|j: int| 0 <= j < i ==> l[j] == j
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate),
        i as nat <= result,
        result <= l.len() as nat
    decreases l.len() - i
{
    if i == l.len() {
        i as nat
    } else if l[i] == i as nat {
        smallest_missing_from(l, i + 1)
    } else {
        i as nat
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call spec helper starting at index 0int */
    smallest_missing_from(l, 0int)
}
// </vc-code>

}
fn main() {}