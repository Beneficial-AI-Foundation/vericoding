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
        forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
        // If index is valid, it's the first occurrence
        0 <= index < arr.len() ==> forall i :: 0 <= i < index ==> arr.spec_index(i) != target
{
    if arr.len() == 0 {
        return -1;
    }
    
    let mut left: int = 0;
    let mut right: int = arr.len() as int - 1;
    let mut result: int = -1;
    
    while left <= right
        invariant
            0 <= left <= arr.len(),
            -1 <= right < arr.len(),
            forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
            // All elements before left don't contain target or are < target
            forall i :: 0 <= i < left ==> arr.spec_index(i) < target,
            // All elements after right don't contain target or are > target  
            forall i :: right < i < arr.len() ==> arr.spec_index(i) > target,
            // If result is set, it's a valid target position and potentially the first
            result == -1 || (0 <= result < arr.len() && arr.spec_index(result) == target),
            // If result is set, no target exists before it in the processed region
            result != -1 ==> forall i :: 0 <= i < result ==> arr.spec_index(i) < target,
            // If target exists in arr, then either result is set or target is in [left, right]
            (exists i :: 0 <= i < arr.len() && arr.spec_index(i) == target) ==> 
                (result != -1 || exists i :: left <= i <= right && arr.spec_index(i) == target)
    {
        let mid = left + (right - left) / 2;
        
        assert(left <= mid <= right);
        assert(0 <= mid < arr.len() as int);
        
        if arr[mid as usize] < target {
            left = mid + 1;
        } else if arr[mid as usize] > target {
            right = mid - 1;
        } else {
            // Found target - this could be the first occurrence
            result = mid;
            right = mid - 1; // Continue searching in the left half
            
            // Maintain invariant: no target before result in processed region
            assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
            assert(forall i :: left <= i < mid ==> arr.spec_index(i) < target);
            assert(forall i :: 0 <= i < result ==> arr.spec_index(i) < target);
        }
    }
    
    // Post-loop analysis
    if result != -1 {
        // We found at least one occurrence of target
        assert(0 <= result < arr.len());
        assert(arr.spec_index(result) == target);
        
        // From invariants, we know no target exists before result
        assert(forall i :: 0 <= i < result ==> arr.spec_index(i) < target);
        
        return result;
    } else {
        // Never found target
        // From invariants and the fact that left > right (loop exited)
        // We know elements [0, left) are < target and (right, len) are > target
        // Since left > right, we've eliminated all possible positions
        assert(left > right);
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        assert(forall i :: right < i < arr.len() ==> arr.spec_index(i) > target);
        
        // Since the array is sorted and we've eliminated all positions
        assert(forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) != target);
        return -1;
    }
}

}