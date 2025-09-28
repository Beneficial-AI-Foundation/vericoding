// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added helper function to check element inclusion */
spec fn should_include(x: i32, e: i32) -> bool {
    x <= e
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
/* code modified by LLM (iteration 5): fixed loop variable type, added decreases clause, and fixed invariant indexing */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < v.len() as int
        invariant
            0 <= i <= v.len() as int,
            forall |k: int| 0<=k<result.len() ==> result@[k] <= e && exists |j: int| 0<=j<i && v@[j] == result@[k],
            forall |j: int| 0<=j<i && v@[j] <= e ==> exists |k: int| 0<=k<result.len() && result@[k] == v@[j]
        decreases v.len() as int - i
    {
        if v[i as usize] <= e {
            result.push(v[i as usize]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}