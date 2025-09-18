// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed compilation error by casting target and array elements to `int` in the quantifiers. */
{
    let len: usize = arr.len();
    if len == 0 {
        return -1;
    }

    let mut low: usize = 0;
    let mut high: usize = len - 1;
    let mut result: isize = -1;

    while low <= high
        invariant
            low <= len,
            high < len,
            // loop invariant: elements from 0 to low-1 are less than the target
            forall|i: int| 0 <= i < low as int ==> arr[i as usize] < target,
            // loop invariant: elements from high+1 to len-1 are greater than the target
            forall|i: int| high as int + 1 <= i && i < len as int ==> arr[i as usize] > target,
            // If result is set, it means arr[result] == target and result is a potential first occurrence
            (result >= 0 ==> (result as usize) < len && arr[result as usize] == target),
            // All elements in the array are sorted
            forall|k: int, l: int| 0 <= k < l < len ==> arr[k as usize] <= arr[l as usize],
        decreases if high >= low { high - low } else { 0 }
    {
        let mid: usize = low + (high - low) / 2;
        if arr[mid] == target {
            result = mid as isize;
            // Move to the left to find the first occurrence
            high = if mid == 0 { 0 } else { mid - 1 }; // Prevent underflow for high
        } else if arr[mid] < target {
            // Target is in the right half
            low = mid + 1;
        } else { // arr[mid] > target
            // Target is in the left half
            high = if mid == 0 { 0 } else { mid - 1 }; // Prevent underflow for high
        }
    }
    result as i32
}
// </vc-code>

}
fn main() {}