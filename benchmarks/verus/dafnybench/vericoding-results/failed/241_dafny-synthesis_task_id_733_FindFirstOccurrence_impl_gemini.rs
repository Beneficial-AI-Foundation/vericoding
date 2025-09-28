// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): passing through correct helper */
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &[i32], target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        (0 <= result < arr.len() ==> arr[result as int] == target) &&
        (result == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error in invariant by using a chained comparison */
    let mut low: i32 = 0;
    let mut high: i32 = arr.len() as i32 - 1;

    while low <= high
        invariant
            0 <= low,
            high < arr.len() as i32,
            is_sorted(arr@),
            forall|k: int| 0 <= k < low as int ==> arr@[k] < target,
            forall|k: int| high as int < k < arr.len() as int ==> arr@[k] > target,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if arr[mid as usize] == target {
            return mid;
        } else if arr[mid as usize] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    return -1;
}
// </vc-code>

}
fn main() {}