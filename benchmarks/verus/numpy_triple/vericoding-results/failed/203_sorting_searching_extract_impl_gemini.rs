// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [Retained helper for loop invariant] */
spec fn is_from_valid_subset(val: i8, arr: Seq<i8>, condition: Seq<bool>, len: int) -> bool {
    exists|j: int| 0 <= j < len && condition[j] && val == arr[j]
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
    /* code modified by LLM (iteration 4): [Fixed compilation error by removing illegal spec access from exec code] */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            condition.len() == arr.len(),
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < result@.len() ==> 
                is_from_valid_subset(result@[k], arr@, condition@, i as int),
            forall|j: int| 0 <= j < (i as int) && condition@[j] ==> 
                result@.contains(arr@[j]),
        decreases arr.len() - i
    {
        if condition[i] {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}