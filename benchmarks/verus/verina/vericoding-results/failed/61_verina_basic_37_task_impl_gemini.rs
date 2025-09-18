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
{
    /* code modified by LLM (iteration 2): Replaced `arr.view()@` with `arr@` in invariants to fix compilation error. */
    let mut low: usize = 0;
    let mut high: usize = arr.len();

    while low < high
        invariant
            0 <= low <= high <= arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr@[i] <= arr@[j],
            forall|i: int| 0 <= i < low as int ==> arr@[i] < target,
            forall|i: int| high as int <= i < arr.len() ==> arr@[i] >= target,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }

    if low < arr.len() && arr[low] == target {
        low as i32
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}