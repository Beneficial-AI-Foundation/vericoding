use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to find the maximum element in a range [start, end]
fn find_max(arr: &[i32], start: usize, end: usize) -> (max_val: i32)
    requires
        arr.len() > 0,
        start <= end < arr.len(),
    ensures
        exists|i: int| start <= i <= end && arr[i as int] == max_val,
        forall|i: int| start <= i <= end ==> arr[i as int] <= max_val,
{
    let mut max = arr[start as usize];
    let mut j = start;
    
    while j <= end
        invariant
            start <= j <= end + 1,
            exists|i: int| start <= i < j && arr[i as int] == max,
            forall|i: int| start <= i < j ==> arr[i as int] <= max,
    {
        if j <= end && arr[j as usize] > max {
            max = arr[j as usize];
        }
        j = j + 1;
    }
    
    max
}

// Helper function to find the minimum element in a range [start, end]
fn find_min(arr: &[i32], start: usize, end: usize) -> (min_val: i32)
    requires
        arr.len() > 0,
        start <= end < arr.len(),
    ensures
        exists|i: int| start <= i <= end && arr[i as int] == min_val,
        forall|i: int| start <= i <= end ==> arr[i as int] >= min_val,
{
    let mut min = arr[start as usize];
    let mut j = start;
    
    while j <= end
        invariant
            start <= j <= end + 1,
            exists|i: int| start <= i < j && arr[i as int] == min,
            forall|i: int| start <= i < j ==> arr[i as int] >= min,
    {
        if j <= end && arr[j as usize] < min {
            min = arr[j as usize];
        }
        j = j + 1;
    }
    
    min
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // Find max in [0, p]
    let max_left = find_max(arr, 0, p);
    
    // Find min in (p, arr.len())
    if p + 1 >= arr.len() {
        // No elements after p, so condition is vacuously true
        return true;
    }
    
    let min_right = find_min(arr, p + 1, arr.len() - 1);
    
    // Check if all elements in left are less than all in right
    let result = max_left < min_right;
    
    // Prove the postcondition
    proof {
        if result {
            // max_left < min_right
            assert forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() implies arr[k as int] < arr[l as int] by {
                // arr[k] <= max_left < min_right <= arr[l]
                assert(arr[k as int] <= max_left);
                assert(min_right <= arr[l as int]);
                assert(max_left < min_right);
            }
        } else {
            // max_left >= min_right, so there exist k and l violating the condition
            assert(exists|k: int| 0 <= k <= p && arr[k as int] == max_left);
            assert(exists|l: int| p < l < arr.len() && arr[l as int] == min_right);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}