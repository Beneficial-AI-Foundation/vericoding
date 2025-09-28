// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger placement in quantifier */
    let mut i = 0usize;
    let mut j = 0usize;
    let mut result: Vec<i32> = Vec::with_capacity(arr1.len() + arr2.len());
    while i < arr1.len() || j < arr2.len()
        invariant
            0 <= i as int <= arr1.len() as int,
            0 <= j as int <= arr2.len() as int,
            result.len() as int == i as int + j as int,
            forall|k: int| 0 <= k < (result.len() as int) - 1 ==> #[trigger] result[k] <= #[trigger] result[k+1],
            (result.len() == 0 || (i < arr1.len() ==> result[(result.len()-1) as int] <= arr1[i as int])),
            (result.len() == 0 || (j < arr2.len() ==> result[(result.len()-1) as int] <= arr2[j as int])),
        decreases (arr1.len() as int + arr2.len() as int) - (i as int + j as int)
    {
        if j >= arr2.len() || (i < arr1.len() && arr1[i] <= arr2[j]) {
            result.push(arr1[i]);
            i += 1;
        } else {
            result.push(arr2[j]);
            j += 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}