// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): fixed exec-mode indexing in spec context */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result@[k] <= e && v@.contains(result@[k]),
            forall |j:int| 0 <= j < i && v@[j] <= e ==> result@.contains(v@[j]),
            forall |k1:int, k2:int| 0 <= k1 < k2 < result.len() ==> result@[k1] != result@[k2],
        decreases v.len() - i,
    {
        let ghost old_result = result@;
        if v[i] <= e {
            result.push(v[i]);
            assert forall |j: int| 0 <= j < i && v@[j] <= e implies old_result.contains(v@[j]) by {}
            assert(v@.contains(v@[i as int]));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}