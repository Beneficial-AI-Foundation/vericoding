// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate stating vector has no duplicates */
spec fn vec_nodup(v: Vec<i32>) -> bool {
    forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v@[k1] != v@[k2]
}
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)

    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],

    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate, push elements <= e, prove invariants including new element contained */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            forall |k:int| 0 <= k < result.len() as int ==> result@[k] <= e && v@.contains(result@[k]),
            forall |j:int| 0 <= j < i as int ==> (v@[j] <= e ==> result@.contains(v@[j])),
        decreases v.len() - i
    {
        let x: i32 = v[i];
        if x <= e {
            result.push(x);
            proof {
                let new_idx: int = result.len() as int - 1;
                assert(0 <= new_idx && new_idx < result.len() as int);
                assert(result@[new_idx] == x);
                assert(result@.contains(x));
            }
        } else {
            proof { }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}