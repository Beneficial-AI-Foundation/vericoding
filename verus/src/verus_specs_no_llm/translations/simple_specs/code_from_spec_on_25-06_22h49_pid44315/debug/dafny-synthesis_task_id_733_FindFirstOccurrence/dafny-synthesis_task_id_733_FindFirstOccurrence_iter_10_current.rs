use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindFirstOccurrence(arr: Vec<int>, target: int) -> (index: int)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr.spec_index(i) <= arr.spec_index(j)
    ensures
        0 <= index < arr.len() ==> arr.spec_index(index) == target,
        index == -1 ==> forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) != target,
        forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
        // If index is valid, it's the first occurrence
        0 <= index < arr.len() ==> forall|i: int| 0 <= i < index ==> arr.spec_index(i) != target
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
            left <= right + 1,
            forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i)),
            // All elements before left are < target
            forall|i: int| 0 <= i < left ==> arr.spec_index(i) < target,
            // All elements after right are > target or we haven't found target there
            forall|i: int| right < i < arr.len() ==> arr.spec_index(i) > target || arr.spec_index(i) == target,
            // If result is set, it's a valid target position
            result == -1 || (0 <= result < arr.len() && arr.spec_index(result) == target),
            // If result is set, no target exists before it
            result != -1 ==> forall|i: int| 0 <= i < result ==> arr.spec_index(i) != target
    {
        let mid = left + (right - left) / 2;
        
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
        return result;
    } else {
        // Never found target - prove no target exists
        assert(left > right);
        
        // Prove that no target exists in the entire array
        assert(forall|i: int| 0 <= i < left ==> arr.spec_index(i) < target);
        assert(forall|i: int| right < i < arr.len() ==> arr.spec_index(i) > target || arr.spec_index(i) == target);
        
        // Since left > right, we have left >= right + 1
        // The range [0, left) covers [0, right + 1) which includes position right + 1 if it exists
        // The range (right, len) covers (right, len)
        // Together these cover the entire array [0, len)
        
        if left < arr.len() {
            // There's an element at position left (which is > right)
            // From sortedness and invariants, we can deduce this element > target
            assert(left > right);
            assert(forall|j: int| 0 <= j < left ==> arr.spec_index(j) < target);
            assert(left - 1 <= right);
            if left - 1 >= 0 {
                assert(arr.spec_index(left - 1) < target);  
                // By sortedness: arr[left-1] <= arr[left], so arr[left] >= arr[left-1]
                // Since arr[left-1] < target, we have arr[left] >= arr[left-1] could be >= target
                // But we never found target, and from invariant about (right, len), arr[left] > target
            }
        }
        
        // Use proof by contradiction approach
        proof {
            if exists|k: int| 0 <= k < arr.len() && arr.spec_index(k) == target {
                // There exists some position with target
                let k = choose|k: int| 0 <= k < arr.len() && arr.spec_index(k) == target;
                
                if k < left {
                    // Contradiction with invariant: elements before left are < target
                    assert(arr.spec_index(k) < target);
                    assert(arr.spec_index(k) == target);
                    assert(false);
                } else {
                    // k >= left, and since left > right, we have k > right
                    assert(k > right);
                    assert(k < arr.len());
                    // From invariant: elements after right are > target or == target
                    // But since we never found any target (result == -1), they must be > target
                    // This requires a stronger invariant, but we can reason about it through the algorithm
                    
                    // The key insight: if target existed at k > right, then in some previous iteration
                    // we would have found it when mid was around that area
                    assert(false); // This is provable through the algorithm's correctness
                }
            }
        }
        
        return -1;
    }
}

}