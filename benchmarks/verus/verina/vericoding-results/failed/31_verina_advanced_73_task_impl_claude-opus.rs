// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn smallest_missing(l: Seq<nat>) -> nat
    decreases l.len()
{
    smallest_missing_helper(l, 0)
}

/* helper modified by LLM (iteration 5): recursive spec function to find smallest missing natural */
spec fn smallest_missing_helper(l: Seq<nat>, candidate: nat) -> nat
    decreases l.len() + 100 - candidate
{
    if l.contains(candidate) {
        smallest_missing_helper(l, candidate + 1)
    } else {
        candidate
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
    /* code modified by LLM (iteration 5): spec function body for finding smallest missing */
    smallest_missing_helper(l, 0)
}
// </vc-code>

}
fn main() {}