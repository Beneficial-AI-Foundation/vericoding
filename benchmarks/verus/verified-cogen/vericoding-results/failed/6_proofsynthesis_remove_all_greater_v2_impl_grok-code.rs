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
    /* code modified by LLM (iteration 5): adjusted trigger annotations for loop invariants to align triggers with postcondition quantifier triggers for better SMT solving */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall |k:int| #![trigger v@.contains(result[k])] 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| #![trigger result@.contains(v[k])] (0 <= k < i && v[k] <= e ==> result@.contains(v[k])),
        decreases v.len() - i
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}