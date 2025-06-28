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
    
    let mut left: int = 0;
    let mut right: int = arr.len() as int;
    let mut result: int = -1;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            forall i :: 0 <= i < left ==> arr.spec_index(i) < target,
            forall i :: right <= i < arr.len() ==> arr.spec_index(i) > target,
            forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
            // If result is set, it points to a target occurrence
            result != -1 ==> (0 <= result < arr.len() && arr.spec_index(result) == target),
            // If result is set, it's in the range [left, right)
            result != -1 ==> (left <= result < right),
            // If result is set, everything before left is < target
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
            // Found target
            result = mid;
            right = mid; // Continue searching in the left half for earlier occurrences
        }
    }
    
    // At this point left == right
    assert(left == right);
    
    if result != -1 {
        // We found the target
        assert(arr.spec_index(result) == target);
        assert(left <= result);
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        
        // Since result >= left and everything before left is < target,
        // we need to show result is the first occurrence
        proof {
            // Everything before left is < target (from invariant)
            assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
            
            // For positions between left and result, use sorted property
            assert forall i :: left <= i < result implies arr.spec_index(i) < target by {
                // Since array is sorted and arr[result] == target
                assert(arr.spec_index(i) <= arr.spec_index(result));
                assert(arr.spec_index(result) == target);
                
                // If arr[i] == target, then our algorithm would have found it
                // and moved right to i, making result <= i. But we have i < result.
                // This means arr[i] != target, so arr[i] < target.
                if arr.spec_index(i) == target {
                    // This leads to a contradiction with our algorithm
                    // When we find a target, we set right = mid to search left
                    // So we would have found this earlier occurrence
                    assert(false);
                }
            }
        }
        
        return result;
    } else {
        // We never found the target
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        assert(forall i :: right <= i < arr.len() ==> arr.spec_index(i) > target);
        assert(left == right);
        
        // Since left == right, we have partitioned the array into:
        // [0, left) where all elements < target
        // [left, len) where all elements > target
        // Therefore, no element equals target
        
        proof {
            assert forall i :: 0 <= i < arr.len() implies arr.spec_index(i) != target by {
                if i < left {
                    assert(arr.spec_index(i) < target);
                } else {
                    assert(left <= i < arr.len());
                    assert(arr.spec_index(i) > target);
                }
            }
        }
        
        return -1;
    }
}

}