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
{
    /* code modified by LLM (iteration 5): Fixed type mismatches by using usize for indexing */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
            forall |k1:int,k2:int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
            forall |j:int| 0 <= j < result.len() ==> exists |m:int| 0 <= m < i && v[m] == result[j] && v[m] <= e,
        decreases v.len() - i
    {
        if v[i as int] <= e {
            let old_result = result;
            result.push(v[i as int]);
            proof {
                assert(result@.len() == old_result@.len() + 1);
                assert(result[result@.len() - 1] == v[i as int]);
                assert(forall |k:int| 0 <= k < old_result.len() ==> result[k] == old_result[k]);
                assert(forall |k:int| 0 <= k < result.len() - 1 ==> result[k] == old_result[k]);
                assert(result@.contains(v[i as int]));
                assert(forall |k:int| 0 <= k < i + 1 && v[k] <= e ==> result@.contains(v[k]));
                assert(forall |j:int| 0 <= j < old_result.len() ==> result[j] != v[i as int]) by {
                    assert(forall |m:int| 0 <= m < i ==> v[m] != v[i as int]);
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}