// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed trigger syntax - triggers must be function calls */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < arr1.len() || j < arr2.len()
        invariant
            i <= arr1.len(),
            j <= arr2.len(),
            result.len() == i + j,
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] <= result[l],
            forall|k: int| 0 <= k < i ==> #[trigger] arr1[k] <= result[result.len() - 1],
            forall|k: int| 0 <= k < j ==> #[trigger] arr2[k] <= result[result.len() - 1],
            i < arr1.len() ==> forall|k: int| 0 <= k < result.len() ==> result[k] <= arr1[i as int],
            j < arr2.len() ==> forall|k: int| 0 <= k < result.len() ==> result[k] <= arr2[j as int],
        decreases arr1.len() + arr2.len() - i - j
    {
        if i < arr1.len() && (j >= arr2.len() || arr1[i] <= arr2[j]) {
            result.push(arr1[i]);
            i = i + 1;
        } else {
            result.push(arr2[j]);
            j = j + 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}