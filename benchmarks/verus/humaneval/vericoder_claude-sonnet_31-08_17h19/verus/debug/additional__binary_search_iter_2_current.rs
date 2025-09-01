use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if arr.len() == 0 {
        return None;
    }
    
    let mut left: usize = 0;
    let mut right: usize = arr.len() - 1;
    
    while left <= right
        invariant
            left <= arr.len(),
            right < arr.len(),
            forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
            forall|i: int| 0 <= i && i < left ==> arr[i] < target,
            forall|i: int| right < i && i < arr.len() ==> arr[i] > target,
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            if mid == arr.len() - 1 {
                break;
            }
            left = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            right = mid - 1;
        }
    }
    
    None
}
// </vc-code>

fn main() {}
}