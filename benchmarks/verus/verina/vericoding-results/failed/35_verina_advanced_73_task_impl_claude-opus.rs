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
    /* code modified by LLM (iteration 5): fix type errors by using usize throughout and only converting in spec contexts */
    let mut i: usize = 0;
    let mut missing: usize = 0;
    
    while i < l.len()
        invariant
            i <= l.len(),
            missing <= i,
            forall|j: nat| j < missing as nat ==> l.contains(j),
            forall|j: int| 0 <= j < i ==> l[j] >= j as nat,
            missing as nat == i as nat || (i < l.len() && l[i as int] > missing as nat),
        decreases l.len() - i,
    {
        if l[i] == missing {
            proof {
                assert(l[i as int] == missing as nat);
            }
            missing = missing + 1;
        } else {
            proof {
                assert(l[i as int] > missing as nat);
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(!l.contains(missing as nat)) by {
            if l.contains(missing as nat) {
                let idx = choose|idx: int| 0 <= idx < l.len() && l[idx] == missing as nat;
                assert(idx >= i as int);
                assert(l[idx as int] >= idx as nat);
                assert(missing as nat >= i as nat);
                assert(false);
            }
        }
    }
    
    missing
}
// </vc-code>

}
fn main() {}