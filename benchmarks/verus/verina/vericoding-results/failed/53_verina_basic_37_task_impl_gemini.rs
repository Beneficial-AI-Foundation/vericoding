// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
    /* code modified by LLM (iteration 5): fixed mismatched types error in invariant */
    let len = arr.len();
    if len == 0 {
        return -1;
    }

    let mut low: i32 = 0;
    let mut high: i32 = (len - 1) as i32;
    let mut result: i32 = -1;

    while low <= high
        invariant
            arr.len() == len,
            0 <= low,
            (low as int) <= len,
            -1 <= (high as int),
            (high as int) < len,
            forall|i: int, j: int| 0 <= i < j < len ==> arr[i] <= arr[j],
            result == -1 || (
                0 <= result && (result as int) < len && arr[result as int] == target
                && (high as int) < (result as int)
            ),
            forall|k: int| 0 <= k < (low as int) ==> arr[k] < target,
            forall|k: int| (high as int) < k < len ==> 
                (result != -1 ==> arr[k] >= target) && (result == -1 ==> arr[k] > target)
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if arr[mid as usize] < target {
            low = mid + 1;
        } else if arr[mid as usize] > target {
            high = mid - 1;
        } else {
            result = mid;
            high = mid - 1;
        }
    }

    return result;
}
// </vc-code>

}
fn main() {}