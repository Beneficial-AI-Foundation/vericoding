// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(arr: &Vec<i32>) -> bool {
    forall|i: int| 0 <= i < arr.len() - 1 ==> arr[i] <= arr[i + 1]
}

spec fn has_no_duplicates(arr: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]
}

spec fn contains_same_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> bool {
    forall|x: i32| arr1@.contains(x) <==> arr2@.contains(x)
}
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut sorted_arr = arr.clone();
    
    // Sort the array
    let mut i = 0;
    while i < sorted_arr.len() {
        let mut j = i + 1;
        while j < sorted_arr.len() {
            if sorted_arr[i] > sorted_arr[j] {
                let temp = sorted_arr[i];
                sorted_arr.set(i, sorted_arr[j]);
                sorted_arr.set(j, temp);
            }
            j += 1;
        }
        i += 1;
    }
    
    // Remove duplicates
    if sorted_arr.len() > 0 {
        result.push(sorted_arr[0]);
        let mut i = 1;
        while i < sorted_arr.len() {
            if sorted_arr[i] != sorted_arr[i - 1] {
                result.push(sorted_arr[i]);
            }
            i += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}