// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected sequence indexing to use @ with int indices */
spec fn elems_leq_and_from_v(res: Vec<i32>, v: Vec<i32>, e: i32) -> bool { forall |k:int| 0 <= k < res.len() as int ==> res@[k] <= e && v@.contains(res@[k]) }
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
    /* code modified by LLM (iteration 5): use usize loop index to avoid int in runtime expressions and maintain invariants matching spec */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            forall |k:int| 0 <= k < result.len() as int ==> result@[k] <= e && v@.contains(result@[k]),
            forall |k:int| 0 <= k < i as int ==> v@[k] <= e ==> result@.contains(v@[k]),
            i <= v.len(),
        decreases v.len() - i
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}