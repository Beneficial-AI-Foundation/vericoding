// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed as no helper functions are needed for this problem. */
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
/* code modified by LLM (iteration 4): Changed variable types to `i32` for consistency and fixed `len` calculation for `high`. */
{
    let len = arr.len() as i32;
    if len == 0 {
        return -1;
    }

    let mut low: i32 = 0;
    let mut high: i32 = len - 1;
    let mut last_idx: i32 = -1;

    while low <= high
        invariant
            0 <= low,
            high < len,
            low <= len,
            -1 <= high,
            last_idx == -1 || (0 <= last_idx < len && arr[last_idx as usize] == elem),
            forall|k: int| 0 <= k < low && arr[k as usize] == elem ==> k as i32 <= last_idx,
            forall|k: int| high < k < len ==> arr[k as usize] != elem || (last_idx != -1 && last_idx >= k as i32),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    {
        let mid: i32 = low + (high - low) / 2;

        if arr[mid as usize] == elem {
            last_idx = mid;
            low = mid + 1;
        } else if arr[mid as usize] < elem {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    last_idx
}
// </vc-code>

}
fn main() {}