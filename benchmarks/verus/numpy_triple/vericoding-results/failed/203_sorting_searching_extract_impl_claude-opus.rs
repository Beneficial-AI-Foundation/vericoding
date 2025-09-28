// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn extract(condition: &Vec<bool>, arr: &Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result@.len() ==>
            exists|i: int| 0 <= i < arr@.len() && condition@[i] == true && #[trigger] result@[k] == arr@[i],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition@.len() && condition@[i] == true ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added trigger annotations to fix quantifier trigger inference */
    let mut result = Vec::new();
    let n = condition.len();
    let mut i = 0;
    let ghost mut processed_indices: Seq<int> = seq![];
    
    while i < n
        invariant
            i <= n,
            n == condition.len(),
            n == arr.len(),
            processed_indices.len() == result@.len(),
            forall|k: int| 0 <= k < result@.len() ==>
                0 <= processed_indices[k] < i && condition@[processed_indices[k]] == true && #[trigger] result@[k] == arr@[processed_indices[k]],
            forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() ==>
                processed_indices[k1] < processed_indices[k2],
            forall|j: int| 0 <= j < i && condition@[j] == true ==>
                exists|k: int| 0 <= k < result@.len() && processed_indices[k] == j && #[trigger] result@[k] == arr@[j],
        decreases n - i
    {
        if condition[i] {
            let old_len = result.len();
            result.push(arr[i]);
            proof {
                processed_indices = processed_indices.push(i as int);
            }
        }
        i = i + 1;
    }
    
    assert(i == n);
    assert(forall|k: int| 0 <= k < result@.len() ==>
        exists|j: int| 0 <= j < n && condition@[j] == true && #[trigger] result@[k] == arr@[j]);
    assert(forall|j: int| 0 <= j < n && condition@[j] == true ==>
        exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[j]);
    
    result
}
// </vc-code>


}
fn main() {}