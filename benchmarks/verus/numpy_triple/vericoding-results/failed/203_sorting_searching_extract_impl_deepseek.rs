// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type conversion from int to usize and use proper ghost types */
fn extract_helper(condition: &Vec<bool>, arr: &Vec<i8>, i: int, result: &mut Vec<i8>)
    requires
        0 <= i <= condition@.len(),
        condition@.len() == arr@.len(),
        forall|k: int| 0 <= k < result@.len() ==> exists|l: int| 0 <= l < i && condition@[l] == true && #[trigger] result@[k] == arr@[l],
        forall|l: int| 0 <= l < i && condition@[l] == true ==> exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[l]
    ensures
        forall|k: int| 0 <= k < result@.len() ==> exists|l: int| 0 <= l < condition@.len() && condition@[l] == true && #[trigger] result@[k] == arr@[l],
        forall|l: int| 0 <= l < condition@.len() && condition@[l] == true ==> exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[l]
{
    if i < condition@.len() {
        ghost {
            if condition@[i] {
                result.push(ghost arr[i as usize]);
            }
        }
        extract_helper(condition, arr, i + 1, result);
    }
}
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
    /* code modified by LLM (iteration 5): use ghost types and recursive helper with proper parameters */
    let mut result = Vec::new();
    proof {
        extract_helper(condition, arr, 0, &mut result);
    }
    result
}
// </vc-code>


}
fn main() {}