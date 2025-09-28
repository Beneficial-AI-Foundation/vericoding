// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide vec_seq to access Seq view of Vec for specs */
spec fn vec_seq(v: &Vec<nat>) -> Seq<nat> {
    v@
}

/* helper modified by LLM (iteration 5): relate Seq view indexing to itself without nested proof block */
proof fn vec_seq_index_equiv(v: &Vec<nat>, i: int)
    requires 0 <= i && i < (v@).len()
    ensures vec_seq(v)[i] == (v@)[i]
{
    assert(vec_seq(v)[i] == (v@)[i]);
}

// </vc-helpers>

// <vc-spec>
fn remove_element(lst: &Vec<nat>, target: nat) -> (result: Vec<nat>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] != target,
        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < lst.len() && #[trigger] lst[j] == #[trigger] result[i] && lst[j] != target,
        forall|i: int, j: int| 0 <= i < j < lst.len() && lst[i] != target && lst[j] != target ==> 
            exists|k1: int, k2: int| 0 <= k1 < k2 < result.len() && 
            result[k1] == lst[i] && result[k2] == lst[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement removal by iterating, pushing non-targets, and discharging invariants */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            i <= lst.len(),
            forall |p: int| 0 <= p && p < (result@).len() ==> exists |t: int| 0 <= t && t < (i as int) && (lst@)[t] != target && (result@)[p] == (lst@)[t],
            forall |j1: int, j2: int| 0 <= j1 && j1 < j2 && (j2 as int) < (i as int) && (lst@)[j1] != target && (lst@)[j2] != target ==> exists |k1: int, k2: int| 0 <= k1 && k1 < k2 && k2 < (result@).len() && (result@)[k1] == (lst@)[j1] && (result@)[k2] == (lst@)[j2],
        decreases (lst.len() as int) - (i as int)
    {
        if lst[i] != target {
            result.push(lst[i]);
            proof {
                assert({
                    forall |p: int|
                        0 <= p && p < (result@).len() ==> exists |t: int| 0 <= t && t < ((i as int) + 1) && (lst@)[t] != target && (result@)[p] == (lst@)[t]
                });
                assert({
                    forall |j1: int, j2: int|
                        0 <= j1 && j1 < j2 && j2 < ((i as int) + 1) && (lst@)[j1] != target && (lst@)[j2] != target ==> exists |k1: int, k2: int| 0 <= k1 && k1 < k2 && k2 < (result@).len() && (result@)[k1] == (lst@)[j1] && (result@)[k2] == (lst@)[j2]
                });
            }
        }
        i += 1;
    }
    proof {
        assert({
            forall |p: int| 0 <= p && p < (result@).len() ==> (result@)[p] != target
        });
        assert({
            forall |p: int| 0 <= p && p < (result@).len() ==> exists |j: int| 0 <= j && j < (lst@).len() && (lst@)[j] == (result@)[p] && (lst@)[j] != target
        });
        assert({
            forall |i1: int, j1: int| 0 <= i1 && i1 < j1 && j1 < (lst@).len() && (lst@)[i1] != target && (lst@)[j1] != target ==> exists |k1: int, k2: int| 0 <= k1 && k1 < k2 && k2 < (result@).len() && (result@)[k1] == (lst@)[i1] && (result@)[k2] == (lst@)[j1]
        });
    }
    result
}

// </vc-code>

}
fn main() {}