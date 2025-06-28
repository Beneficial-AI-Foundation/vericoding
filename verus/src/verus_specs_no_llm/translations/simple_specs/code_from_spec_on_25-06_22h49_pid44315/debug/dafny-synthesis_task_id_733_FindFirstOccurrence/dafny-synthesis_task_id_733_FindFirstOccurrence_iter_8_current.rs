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
            // All elements before left are < target
            forall i :: 0 <= i < left ==> arr.spec_index(i) < target,
            // All elements after right are > target  
            forall i :: right < i < arr.len() ==> arr.spec_index(i) > target,
            // If result is set, it's a valid target position
            result == -1 || (left <= result <= right && arr.spec_index(result) == target),
            // If result is set, all positions after result in current range are >= target
            result != -1 ==> forall i :: result < i <= right ==> arr.spec_index(i) >= target
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
        }
    }
    
    // Post-loop analysis
    if result != -1 {
        // We found at least one occurrence of target
        assert(0 <= result < arr.len());
        assert(arr.spec_index(result) == target);
        
        // Prove this is the first occurrence
        // From invariants: all elements before left are < target
        // Since result was found and right = result - 1 in last iteration,
        // and left > right now, we have left > result
        // But result was in range [left, right] when found
        // The binary search ensures result is the leftmost occurrence
        
        // Key insight: when we find target, we set right = mid - 1
        // This ensures we keep searching left for earlier occurrences
        // When loop exits, result holds the leftmost occurrence found
        
        assert(forall i :: 0 <= i < result ==> arr.spec_index(i) < target);
        
        return result;
    } else {
        // Never found target
        // From invariants: elements before left are < target
        // elements after right are > target
        // Since left > right, we've covered all elements
        assert(forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) != target);
        return -1;
    }
}

}