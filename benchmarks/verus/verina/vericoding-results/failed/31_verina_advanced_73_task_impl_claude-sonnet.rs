// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): moved ghost variable usage into proof blocks to fix compilation errors */
    let mut i: usize = 0;
    let len_usize = l.len() as usize;
    while i < len_usize
        invariant
            forall|candidate: nat| candidate < i ==> l.contains(candidate),
            i <= l.len()
        decreases len_usize - i
    {
        proof {
            let ghost_i = i as nat;
            let ghost_val = l[i as int];
            if ghost_val != ghost_i {
                assert(!l.contains(ghost_i));
                return ghost_i;
            }
        }
        i = i + 1;
    }
    proof {
        let result = i as nat;
        assert(!l.contains(result));
        return result;
    }
}
// </vc-code>

}
fn main() {}