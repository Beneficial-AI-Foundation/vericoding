// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use sequence notation @ for array indexing */
fn binary_search_preserves_sorted(arr: &Vec<i32>, left: usize, right: usize) -> bool
    requires
        left <= right,
        right <= arr.len(),
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr@[i] <= arr@[j],
{
    forall|i: int, j: int| left <= i < j < right ==> arr@[i] <= arr@[j]
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> {
            &&& 0 <= result < arr.len()
            &&& arr[result as int] == target
            &&& forall|i: int| 0 <= i < result ==> arr[i] != target
        }) &&
        (result == -1 ==> {
            &&& forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
        }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use sequence notation @ for array indexing */
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    let mut result: i32 = -1;
    
    while left < right
        invariant
            left <= right,
            right <= arr.len(),
            forall|i: int| 0 <= i < left ==> arr@[i] != target,
            result == -1 || (0 <= result < arr.len() && arr@[result as int] == target && forall|i: int| 0 <= i < result ==> arr@[i] != target),
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == target {
            result = mid as i32;
            right = mid;
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    if result >= 0 {
        result
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}