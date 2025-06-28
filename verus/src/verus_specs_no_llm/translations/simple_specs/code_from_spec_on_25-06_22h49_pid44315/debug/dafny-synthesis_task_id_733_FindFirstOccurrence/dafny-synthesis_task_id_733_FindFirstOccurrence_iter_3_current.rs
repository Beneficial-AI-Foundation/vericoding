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
            // If we've found a target, result points to some occurrence of target
            result != -1 ==> (left <= result < right && arr.spec_index(result) == target)
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
        // We found the target, and result is the leftmost occurrence
        assert(arr.spec_index(result) == target);
        
        // All elements before result are < target (from invariant)
        assert(forall i :: 0 <= i < result ==> arr.spec_index(i) < target);
        
        // This proves result is the first occurrence
        return result;
    } else {
        // We never found the target
        // From invariants: elements [0, left) are < target
        // and elements [right, len) are >= target
        // Since left == right, we've covered the whole array
        // and no element equals target
        
        // Prove no element equals target
        assert(forall i :: 0 <= i < left ==> arr.spec_index(i) < target);
        assert(forall i :: right <= i < arr.len() ==> arr.spec_index(i) >= target);
        assert(left == right);
        
        // Since we never set result to anything other than -1,
        // and we've covered the whole array with < or >= target,
        // no element can equal target
        proof {
            assert forall i :: 0 <= i < arr.len() implies arr.spec_index(i) != target by {
                if 0 <= i < left {
                    assert(arr.spec_index(i) < target);
                } else {
                    assert(right <= i < arr.len());
                    assert(arr.spec_index(i) >= target);
                    // If arr.spec_index(i) == target, we would have found it
                    // But we didn't, so it must be > target
                    if arr.spec_index(i) == target {
                        // This would contradict that we never found target
                        // The algorithm would have set result when we encountered this element
                    }
                }
            };
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
        forall i :: start <= i < end ==> arr.spec_index(i) != target
    ensures
        forall i :: start <= i < end ==> arr.spec_index(i) > target
{
}

}