// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added sortedness property to loop invariant */
fn lower_bound(slice: &[i32], target: i32) -> (result: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < slice.len() ==> slice[i] <= slice[j],
    ensures
        0 <= result <= slice.len(),
        forall|k: int| 0 <= k < result ==> slice[k] < target,
        forall|k: int| result <= k < slice.len() ==> slice[k] >= target,
{
    let mut low: usize = 0;
    let mut high: usize = slice.len();

    while low < high
        invariant
            0 <= low <= high <= slice.len(),
            forall|k: int| 0 <= k < low ==> slice[k] < target,
            forall|k: int| high <= k < slice.len() ==> slice[k] >= target,
            forall|i: int, j: int| 0 <= i < j < slice.len() ==> slice[i] <= slice[j],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if slice[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (index: Option<usize>)

    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],

    ensures
        if let Some(idx) = index {
            &&& 0 <= idx < arr.len()
            &&& forall|k: int| 0 <= k < idx ==> arr[k] != target
            &&& arr[idx as int] == target
        } else {
            forall|k: int| 0 <= k < arr.len() ==> arr[k] != target
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The logic correctly uses the helper, so no change is needed. */
{
    let idx = lower_bound(arr, target);
    if idx < arr.len() && arr[idx] == target {
        Some(idx)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}