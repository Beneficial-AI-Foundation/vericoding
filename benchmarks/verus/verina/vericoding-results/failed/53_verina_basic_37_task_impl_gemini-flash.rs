// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions are needed for this problem. */

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
/* code modified by LLM (iteration 5): Corrected type mismatches in invariant conditions by casting `arr[idx]` from `int` to `i32` when comparing with `target`. Ensured all array accesses `arr[_]` are done with `int` indices as per Verus requirements. */
{
    let len = arr.len();
    if len == 0 {
        return -1;
    }

    let mut low: usize = 0;
    let mut high: usize = len - 1;
    let mut result: isize = -1;

    while low <= high
        invariant
            0 <= low,
            high < len,
            (result == -1 || (0 <= result as int && (result as int) < len && arr[result as int] == target)),
            forall|i: int| 0 <= i < low ==> (arr[i] != target || (result != -1 && i >= result as int && arr[result as int] == target)),
            forall|i: int| high < i < len ==> arr[i] != target,
        decreases high - low
    {
        let mid: usize = low + (high - low) / 2;
        assert(mid < len);
        if arr[mid as int] == target {
            result = mid as isize;
            if mid == 0 {
                break;
            }
            high = mid - 1;
        } else if arr[mid as int] < target {
            low = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    result as i32
}
// </vc-code>

}
fn main() {}