use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindFirstOccurrence(arr: Vec<int>, target: int) -> (index: int)
    requires
        forall i, j :: 0 <= i < j < arr.len() ==> arr.spec_index(i) <= arr.spec_index(j)
    ensures
        0 <= index < arr.len() ==> arr.spec_index(index) == target,
        index == -1 ==> forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) != target,
        forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i))
{
    if arr.len() == 0 {
        return -1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    let mut result: int = -1;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall i :: 0 <= i < left ==> arr.spec_index(i) < target,
            forall i :: right <= i < arr.len() ==> arr.spec_index(i) > target,
            result == -1 || (0 <= result < arr.len() && arr.spec_index(result) == target),
            forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i))
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] < target {
            left = mid + 1;
        } else if arr[mid] > target {
            right = mid;
        } else {
            // Found target, but we need the first occurrence
            result = mid as int;
            right = mid; // Continue searching in the left half
        }
    }
    
    // Verify we found the first occurrence
    if result != -1 {
        // Check if there's an earlier occurrence
        let mut i: usize = 0;
        while i < result
            invariant
                0 <= i <= result < arr.len(),
                arr.spec_index(result) == target,
                forall j :: 0 <= j < i ==> arr.spec_index(j) != target,
                forall k :: 0 <= k < arr.len() ==> arr.spec_index(k) == old(arr.spec_index(k))
        {
            if arr[i] == target {
                result = i as int;
                break;
            }
            i += 1;
        }
    }
    
    result
}

}