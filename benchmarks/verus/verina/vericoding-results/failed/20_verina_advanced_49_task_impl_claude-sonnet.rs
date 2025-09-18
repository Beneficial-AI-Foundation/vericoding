// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed predicate keyword to spec_fn */
spec fn all_elements_in_result(arr: &Vec<i32>, start: int, result: &Vec<i32>) -> bool
{
    forall|k: int| 0 <= k < start ==> #[trigger] exists|r: int| 0 <= r < result.len() && result[r] == arr[k]
}

spec fn sorted_range(arr: &Vec<i32>, start: int, end: int) -> bool
{
    forall|k1: int, k2: int| start <= k1 < k2 < end ==> #[trigger] arr[k1] <= arr[k2]
}
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
    /* code modified by LLM (iteration 5): using spec_fn helpers for merge sort implementation */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < arr1.len() || j < arr2.len()
        invariant
            i <= arr1.len(),
            j <= arr2.len(),
            result.len() == i + j,
            sorted_range(&result, 0, result.len() as int),
            all_elements_in_result(arr1, i, &result),
            all_elements_in_result(arr2, j, &result),
        decreases arr1.len() + arr2.len() - i - j
    {
        if i >= arr1.len() {
            result.push(arr2[j]);
            j += 1;
        } else if j >= arr2.len() {
            result.push(arr1[i]);
            i += 1;
        } else if arr1[i] <= arr2[j] {
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