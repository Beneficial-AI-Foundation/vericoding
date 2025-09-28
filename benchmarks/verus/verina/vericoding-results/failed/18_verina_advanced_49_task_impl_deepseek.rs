// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed Option type compatibility */
spec fn is_sorted(arr: &Vec<i32>) -> bool
    recommends arr.len() >= 0
{
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

proof fn merge_sorted_maintains_order(arr1: &Vec<i32>, arr2: &Vec<i32>, result: &Vec<i32>, idx1: nat, idx2: nat)
    requires
        is_sorted(arr1),
        is_sorted(arr2),
        idx1 <= arr1.len(),
        idx2 <= arr2.len(),
        is_sorted(result),
        result.len() == idx1 + idx2,
        (idx1 > 0 && idx2 > 0) ==> result.last() == Some(#[trigger] max(arr1[idx1 - 1], arr2[idx2 - 1]) as i32)
    ensures
        is_sorted(result)
{
}

spec fn max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

fn executable_max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
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
/* code modified by LLM (iteration 5): Fixed Option type cast compatibility issue */
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < arr1.len() || j < arr2.len()
        invariant
            is_sorted(&result),
            result.len() == i + j,
            i <= arr1.len(),
            j <= arr2.len(),
            (i > 0 && j > 0) ==> result.last() == Some(#[trigger] max(arr1[i - 1], arr2[j - 1]) as i32)
        decreases (arr1.len() - i) + (arr2.len() - j)
    {
        if i < arr1.len() && j < arr2.len() {
            if arr1[i] <= arr2[j] {
                result.push(arr1[i]);
                i += 1;
            } else {
                result.push(arr2[j]);
                j += 1;
            }
        } else if i < arr1.len() {
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