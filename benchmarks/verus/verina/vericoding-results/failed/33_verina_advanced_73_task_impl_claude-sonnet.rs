// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to check if element is contained in sequence prefix */
spec fn contains_up_to(s: Seq<nat>, elem: nat, bound: nat) -> bool {
    exists|idx: int| 0 <= idx < bound && s[idx] == elem
}

/* helper modified by LLM (iteration 5): lemma about sequence properties under strict ordering */
proof fn sequence_property_lemma(l: Seq<nat>, i: nat)
    requires
        forall|x: int, y: int| 0 <= x < y < l.len() ==> l[x] < l[y],
        i < l.len(),
        l[i as int] != i,
    ensures
        !l.contains(i),
        forall|candidate: nat| candidate < i ==> l.contains(candidate),
{
    // Proof that i is not in the sequence
    if l.contains(i) {
        let idx = choose|k: int| 0 <= k < l.len() && l[k] == i;
        if idx < i {
            assert(l[idx] < l[i as int]);  // contradiction since both equal i
            assert(false);
        } else if idx > i {
            assert(l[i as int] < l[idx]);  // contradiction since both equal i
            assert(false);
        } else {
            assert(l[i as int] == i);  // contradiction with premise
            assert(false);
        }
    }
    
    // Proof that all smaller candidates are in sequence
    assert(forall|candidate: nat| candidate < i ==> {
        if candidate < l.len() {
            l[candidate as int] == candidate
        } else {
            exists|k: int| 0 <= k < l.len() && l[k] == candidate
        }
    });
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
    /* code modified by LLM (iteration 5): use ghost variables and proof blocks to handle nat/int distinction */
    proof {
        let mut i_ghost: nat = 0nat;
        while i_ghost < l.len()
            invariant
                forall|candidate: nat| candidate < i_ghost ==> l.contains(candidate),
                i_ghost <= l.len(),
        {
            if l[i_ghost as int] != i_ghost {
                sequence_property_lemma(l, i_ghost);
                assert(!l.contains(i_ghost));
                assert(forall|candidate: nat| candidate < i_ghost ==> l.contains(candidate));
                return i_ghost;
            }
            i_ghost = i_ghost + 1nat;
        }
        
        // If we reach here, all elements 0..len-1 are present
        assert(forall|candidate: nat| candidate < l.len() ==> l.contains(candidate));
        assert(!l.contains(l.len() as nat));
        l.len() as nat
    }
}
// </vc-code>

}
fn main() {}