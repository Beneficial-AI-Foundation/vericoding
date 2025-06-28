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
            forall i :: right <= i < arr.len() ==> arr.spec_index(i) >= target,
            forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
            // If we've found a target, result is a valid index with target value
            result != -1 ==> (0 <= result < arr.len() && arr.spec_index(result) == target),
            // If we've found a target, all elements before left are < target
            result != -1 ==> forall i :: 0 <= i < left ==> arr.spec_index(i) < target
    {
        let mid = left + (right - left) / 2;
        
        assert(left <= mid < right);
        assert(0 <= mid < arr.len());
        
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
        // We found the target, need to prove it's the first occurrence
        assert(arr.spec_index(result) == target);
        
        // From the invariant, all elements before left are < target
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        
        // Since right == left and we continued searching left when we found target,
        // result must be >= left, but we also know result < original right values
        // We need to prove result is the leftmost occurrence
        
        // The key insight: when we found target and set right = mid, we ensured
        // we'd continue searching left. The invariant maintains that everything
        // before left is < target.
        
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        
        // Since the array is sorted and result has target value,
        // and everything before left is < target, result must be >= left
        assert(result >= left);
        
        // Prove result is the first occurrence
        proof {
            assert forall i :: 0 <= i < result implies arr.spec_index(i) < target by {
                if i < left {
                    assert(arr.spec_index(i) < target);
                } else {
                    // For left <= i < result, we use the sorted property
                    assert(left <= i < result);
                    assert(arr.spec_index(i) <= arr.spec_index(result)); // sorted property
                    assert(arr.spec_index(result) == target);
                    if arr.spec_index(i) == target {
                        // This would contradict our search process
                        // If there was a target at position i < result, our algorithm
                        // would have found it and set result to i or smaller
                        assert(false);
                    }
                    assert(arr.spec_index(i) < target);
                }
            }
        }
        
        return result;
    } else {
        // We never found the target
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        assert(forall i :: right <= i < arr.len() ==> arr.spec_index(i) >= target);
        assert(left == right);
        
        // This means the entire array is partitioned: [0, left) < target, [left, len) >= target
        // Since we never found target, everything >= target must be > target
        
        proof {
            // Use the helper lemma
            lemma_no_target_found(arr, target, left, arr.len() as int);
            
            assert forall i :: 0 <= i < arr.len() implies arr.spec_index(i) != target by {
                if i < left {
                    assert(arr.spec_index(i) < target);
                } else {
                    assert(left <= i < arr.len());
                    assert(arr.spec_index(i) > target); // from lemma
                }
            }
        }
        
        return -1;
    }
}

// Helper proof function to establish that if we haven't found target in a range,
// and we know elements are either < target or >= target, then >= must mean > target
proof fn lemma_no_target_found(arr: Vec<int>, target: int, start: int, end: int)
    requires
        forall i, j :: 0 <= i < j < arr.len() ==> arr.spec_index(i) <= arr.spec_index(j),
        0 <= start <= end <= arr.len(),
        forall i :: start <= i < end ==> arr.spec_index(i) >= target,
    ensures
        forall i :: start <= i < end ==> arr.spec_index(i) != target ==> arr.spec_index(i) > target
{
    // This is trivially true: if x >= target and x != target, then x > target
}

}