use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_sorted(arr: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr@[i] <= arr@[j]
}

spec fn valid_insert_position(arr: &[i32], target: i32, pos: usize) -> bool {
    pos <= arr.len() &&
    (forall|i: int| 0 <= i < pos ==> arr@[i] <= target) &&
    (forall|i: int| pos <= i < arr.len() ==> target <= arr@[i])
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)"
docstring: Perform binary search on a sorted array to find the position where an element should be inserted.
*/
// </vc-description>

// <vc-spec>
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    requires is_sorted(arr)
    ensures match result {
        Some(pos) => pos < arr.len() && arr@[pos as int] == target,
        None => forall|i: int| 0 <= i < arr.len() ==> arr@[i] != target
    }
// </vc-spec>

// <vc-code>
{
    let mut left = 0;
    let mut right = arr.len();
    
    /* code modified by LLM (iteration 4): added decreases clause for loop termination */
    while left < right
        invariant 
            left <= right,
            right <= arr.len(),
            is_sorted(arr),
            forall|i: int| 0 <= i < left ==> arr@[i] < target,
            forall|i: int| right <= i < arr.len() ==> arr@[i] > target
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        /* code modified by LLM (iteration 3): use regular array indexing for exec code */
        if arr[mid] < target {
            left = mid + 1;
        } else if arr[mid] > target {
            right = mid;
        } else {
            return Some(mid);
        }
    }
    
    None
}
// </vc-code>

fn main() {}
}