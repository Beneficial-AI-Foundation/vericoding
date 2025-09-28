// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added explicit triggers for quantifiers to fix automatic trigger inference */
spec fn is_sorted(arr: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn contains_all_elements(result: &Vec<i32>, arr1: &Vec<i32>, arr2: &Vec<i32>) -> bool {
    forall|x: i32| #[trigger] arr1.contains(x) || #[trigger] arr2.contains(x) <==> #[trigger] result.contains(x)
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
    /* code modified by LLM (iteration 5): implementation remains the same as triggers were fixed in helpers */
    let mut result = Vec::new();
    let mut i1 = 0usize;
    let mut i2 = 0usize;
    
    while i1 < arr1.len() || i2 < arr2.len()
        invariant
            i1 <= arr1.len(),
            i2 <= arr2.len(),
            result.len() == i1 + i2,
            is_sorted(&result),
        decreases arr1.len() + arr2.len() - i1 - i2
    {
        if i1 >= arr1.len() {
            result.push(arr2[i2]);
            i2 += 1;
        } else if i2 >= arr2.len() {
            result.push(arr1[i1]);
            i1 += 1;
        } else if arr1[i1] <= arr2[i2] {
            result.push(arr1[i1]);
            i1 += 1;
        } else {
            result.push(arr2[i2]);
            i2 += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}