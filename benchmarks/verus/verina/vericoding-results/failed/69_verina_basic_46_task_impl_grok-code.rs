// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches in ensures by using arr[last_idx as int] and arr[k] instead of usize indexing, ensuring consistency with Verus sequence specs. */
fn last_occurrence(arr: &Vec<i32>, elem: i32) -> (last_idx: i32)
    requires forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr@[i] <= arr@[j],
    ensures
        (last_idx >= 0 ==> 
            0 <= last_idx < arr.len() as i32 &&
            arr[last_idx as int] == elem &&
            forall|k: int| last_idx < k < arr.len() as i32 ==> arr[k] != elem) &&
        (last_idx == -1 ==> forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem),
{
    if arr.len() == 0 {
        return -1;
    }
    let mut left: i32 = 0;
    let mut right: i32 = (arr.len() as i32) - 1;
    while left <= right
        invariant 0 <= left <= right + 1 <= arr.len() as i32,
        decreases (right - left) as int,
    {
        let mid: i32 = left + ((right - left) / 2);
        if arr[mid as usize] <= elem {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }
    if left > 0 {
        let idx = (left - 1) as usize;
        if arr[idx] == elem {
            return (left - 1);
        }
    }
    -1
}
// </vc-helpers>

// <vc-spec>
fn last_position(arr: &Vec<i32>, elem: i32) -> (result: i32)
    requires forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> 
            0 <= result < arr.len() &&
            arr[result as int] == elem &&
            forall|k: int| result < k < arr.len() ==> arr[k] != elem) &&
        (result == -1 ==> forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed as the implementation correctly calls the helper function. */
{
    let result: i32 = last_occurrence(arr, elem);
    result
}
// </vc-code>

}
fn main() {}