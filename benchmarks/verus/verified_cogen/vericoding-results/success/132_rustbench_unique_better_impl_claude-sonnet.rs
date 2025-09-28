// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added trigger annotations to fix quantifier trigger inference */
spec fn is_unique_at(a: &[i32], val: i32, pos: int) -> bool {
    forall|k: int| #![trigger a[k]] 0 <= k < a.len() && k != pos ==> a[k] != val
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added trigger annotations to fix quantifier trigger inference */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k1: int, k2: int| #![trigger result[k1], result[k2]] 0 <= k1 < k2 < result.len() ==> result[k1] < result[k2],
            forall|k: int| #![trigger result[k]] 0 <= k < result.len() ==> exists|j: int| #![trigger a[j]] 0 <= j < i && result[k] == a[j],
        decreases a.len() - i
    {
        if result.len() == 0 || a[i] != result[result.len() - 1] {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}