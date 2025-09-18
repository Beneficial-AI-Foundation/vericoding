// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and array indexing specifications */
proof fn lemma_vec_index(arr: Vec<i32>, i: int)
    requires 0 <= i < arr.len()
    ensures arr[i as usize] == arr@[i]
{
}

spec fn binary_search_last_spec(arr: Seq<i32>, elem: i32, low: int, high: int) -> (result: int)
    requires
        0 <= low <= high <= arr.len(),
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        (result >= 0 ==> 
            0 <= result < arr.len() &&
            arr[result] == elem &&
            forall|k: int| result < k < arr.len() ==> arr[k] != elem) &&
        (result == -1 ==> forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem)
{
    if low >= high {
        -1
    } else {
        let mid = low + (high - low) / 2;
        if arr[mid] < elem {
            binary_search_last_spec(arr, elem, mid + 1, high)
        } else if arr[mid] > elem {
            binary_search_last_spec(arr, elem, low, mid)
        } else {
            if mid + 1 >= arr.len() || arr[mid + 1] > elem {
                mid
            } else {
                binary_search_last_spec(arr, elem, mid + 1, high)
            }
        }
    }
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
/* code modified by LLM (iteration 5): Fixed array indexing types and verification conditions */
{
    let mut low: usize = 0;
    let mut high: usize = arr.len();
    let mut last_found: i32 = -1;
    
    while low < high
        invariant
            low <= high <= arr.len(),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            binary_search_last_spec(arr@, elem, low as int, high as int) == binary_search_last_spec(arr@, elem, 0, arr.len() as int),
            last_found == -1 || (0 <= last_found < arr.len() as int && arr@[last_found] == elem)
    {
        let mid = low + (high - low) / 2;
        if arr[mid] < elem {
            low = mid + 1;
        } else if arr[mid] > elem {
            high = mid;
        } else {
            if mid + 1 >= high || arr[mid + 1] > elem {
                return mid as i32;
            } else {
                low = mid + 1;
                last_found = mid as i32;
            }
        }
    }
    
    -1
}
// </vc-code>

}
fn main() {}