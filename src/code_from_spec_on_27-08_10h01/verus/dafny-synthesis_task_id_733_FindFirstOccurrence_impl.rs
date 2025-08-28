use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_first_occurrence(arr: &[i32], target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    ensures
        (0 <= result < arr.len() ==> arr[result as int] == target) &&
        (result == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] != target)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut left = 0;
    #[verifier::truncate]
    let mut right = arr.len() as i32;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall|i: int| 0 <= i < left ==> arr[i as int] < target,
            forall|i: int| right <= i < arr.len() ==> arr[i as int] >= target
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid as usize] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    #[verifier::truncate]
    if left < arr.len() as i32 && arr[left as usize] == target {
        left
    } else {
        -1
    }
}
// </vc-code>

fn main() {
}

}