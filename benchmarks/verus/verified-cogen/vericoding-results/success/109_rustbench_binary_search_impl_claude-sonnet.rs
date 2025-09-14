// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_between(arr: &[i32], start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i && i < j && j < end ==> arr[i] <= arr[j]
}

spec fn all_different_in_range(arr: &[i32], target: i32, start: int, end: int) -> bool {
    forall|i: int| start <= i && i < end ==> arr[i] != target
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
    if arr.len() == 0 {
        return None;
    }
    
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    
    while left < right
        invariant
            left <= right,
            right <= arr.len(),
            all_different_in_range(arr, target, 0, left as int),
            all_different_in_range(arr, target, right as int, arr.len() as int),
            forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    None
}
// </vc-code>

}
fn main() {}