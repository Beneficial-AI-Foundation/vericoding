use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall|i: int| 0 <= i && i < left ==> arr[i] < target,
            forall|i: int| right <= i && i < arr.len() ==> arr[i] > target,
    {
        let mid: usize = left + (right - left) / 2;
        
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