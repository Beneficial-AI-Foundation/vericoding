// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): converted array accesses to ghost sequence in requires/ensures and used ghost length */
fn binary_search_helper(arr: &[i32], target: i32, low: usize, high: usize) -> (result: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr@.len() ==> arr@[i] <= arr@[j],
        (low as int) <= (high as int),
        (high as int) <= arr@.len(),
        (low == 0 || arr@[(low - 1) as int] < target),
        (high as int == arr@.len() || arr@[high as int] > target),
    ensures
        match result {
            Some(index) => arr@[index as int] == target && (index as int) >= (low as int) && (index as int) < (high as int),
            None => forall|i: int| (low as int) <= i && i < (high as int) ==> arr@[i] != target,
        },
    decreases (high as int - low as int) as int
{
    if low == high {
        None
    } else {
        let mid = low + (high - low) / 2;
        if arr[mid] == target {
            Some(mid)
        } else if arr[mid] < target {
            binary_search_helper(arr, target, mid + 1, high)
        } else {
            binary_search_helper(arr, target, low, mid)
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes needed */
    binary_search_helper(arr, target, 0, arr.len())
}
// </vc-code>

}
fn main() {}