// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed sequence indexing syntax in requires clause */
spec fn sequence_contains_all_below(l: Seq<nat>, bound: nat) -> bool {
    forall|x: nat| x < bound ==> l.contains(x)
}

proof fn lemma_missing_number_bounds(l: Seq<nat>, candidate: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l@[i] < l@[j],
    requires !l.contains(candidate),
    ensures forall|x: nat| x < candidate ==> l.contains(x) || candidate == 0
{
    if candidate > 0 {
        let mut i = 0;
        while i < candidate
            invariant forall|x: nat| x < i ==> l.contains(x)
        {
            if !l.contains(i) {
                assert(i < candidate);
                assert(!l.contains(i));
                return;
            }
            i = i + 1;
        }
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
    /* code modified by LLM (iteration 5): simplified implementation to avoid complex proof requirements */
    let mut candidate: nat = 0;
    loop
        invariant forall|x: nat| x < candidate ==> l.contains(x)
    {
        if !l.contains(candidate) {
            return candidate;
        }
        candidate = candidate + 1;
    }
}
// </vc-code>

}
fn main() {}