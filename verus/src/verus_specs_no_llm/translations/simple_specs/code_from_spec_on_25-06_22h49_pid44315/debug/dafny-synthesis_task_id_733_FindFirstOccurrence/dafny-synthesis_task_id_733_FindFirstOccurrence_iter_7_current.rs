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
    let mut right: int = arr.len() as int;
    let mut result: int = -1;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall i :: 0 <= i < left ==> arr.spec_index(i) < target,
            forall i :: right <= i < arr.len() ==> arr.spec_index(i) >= target,
            forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
            // If result is set, it points to a valid target occurrence
            result == -1 || (0 <= result < arr.len() && arr.spec_index(result) == target),
            // If result is set, it's in the right portion and no target before left
            result != -1 ==> right <= result < arr.len(),
            result != -1 ==> forall i :: 0 <= i < left ==> arr.spec_index(i) < target
    {
        let mid = left + (right - left) / 2;
        
        assert(left <= mid < right);
        assert(0 <= mid < arr.len() as int);
        
        if arr[mid as usize] < target {
            left = mid + 1;
        } else if arr[mid as usize] > target {
            right = mid;
        } else {
            // Found target - this could be the first occurrence
            result = mid;
            right = mid; // Continue searching in the left half for earlier occurrences
        }
    }
    
    // At this point left == right
    assert(left == right);
    
    if result != -1 {
        // We found the target, but result might not be the leftmost
        // We need to check if there's a target at position left-1 or earlier
        
        // Since left == right and we found result with right <= result,
        // we have left <= result
        
        // Check if there's a target at the boundary
        if left > 0 && left <= arr.len() && arr[left as usize - 1] == target {
            // There's a target just before our search boundary
            let mut first_pos = left - 1;
            
            // Linear search backwards to find the first occurrence
            while first_pos > 0 && arr[first_pos as usize - 1] == target
                invariant
                    0 <= first_pos < arr.len(),
                    arr.spec_index(first_pos) == target,
                    forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i))
            {
                first_pos = first_pos - 1;
            }
            
            return first_pos;
        } else if left < arr.len() && arr[left as usize] == target {
            // The target is at position left
            let mut first_pos = left;
            
            // Linear search backwards to find the first occurrence  
            while first_pos > 0 && arr[first_pos as usize - 1] == target
                invariant
                    0 <= first_pos < arr.len(),
                    arr.spec_index(first_pos) == target,
                    forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i))
            {
                first_pos = first_pos - 1;
            }
            
            return first_pos;
        } else {
            // No target found at the boundary
            return -1;
        }
    } else {
        // We never found the target during binary search
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        assert(forall i :: right <= i < arr.len() ==> arr.spec_index(i) >= target);
        assert(left == right);
        
        if left >= arr.len() {
            // All elements are < target
            return -1;
        } else {
            // Check the boundary position
            if arr[left as usize] == target {
                // Found target at boundary position
                let mut first_pos = left;
                
                // This should be the first occurrence since all before left are < target
                assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
                
                return first_pos;
            } else {
                // No target found
                return -1;
            }
        }
    }
}

}