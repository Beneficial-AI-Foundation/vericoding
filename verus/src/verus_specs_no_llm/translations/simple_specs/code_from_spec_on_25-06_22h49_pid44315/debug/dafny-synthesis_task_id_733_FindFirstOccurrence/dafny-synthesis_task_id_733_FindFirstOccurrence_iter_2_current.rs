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
            result == -1 || (0 <= result < arr.len() && arr.spec_index(result) == target),
            forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i))
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid as usize] < target {
            left = mid + 1;
        } else if arr[mid as usize] > target {
            right = mid;
        } else {
            // Found target, this could be the first occurrence
            result = mid;
            right = mid; // Continue searching in the left half for earlier occurrences
        }
    }
    
    // At this point, if result != -1, we need to verify it's actually the first occurrence
    if result != -1 {
        // Since we always move right = mid when we find a target, 
        // and the array is sorted, result should be the first occurrence
        assert(arr.spec_index(result) == target);
        
        // Prove that all elements before result are < target
        assert(forall i :: 0 <= i < result ==> arr.spec_index(i) < target);
        
        // This means result is indeed the first occurrence
    } else {
        // If result == -1, then we never found target
        // The invariant guarantees that all elements < left are < target
        // and all elements >= right are > target
        // Since left == right and we covered the whole array, no element equals target
        assert(forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) != target);
    }
    
    result
}

// Helper lemma to prove properties about sorted arrays
proof fn lemma_sorted_array_property(arr: Vec<int>, i: int, j: int, target: int)
    requires
        forall x, y :: 0 <= x < y < arr.len() ==> arr.spec_index(x) <= arr.spec_index(y),
        0 <= i <= j < arr.len(),
        arr.spec_index(j) < target
    ensures
        arr.spec_index(i) < target
{
    if i < j {
        assert(arr.spec_index(i) <= arr.spec_index(j));
        assert(arr.spec_index(j) < target);
        assert(arr.spec_index(i) < target);
    } else {
        assert(i == j);
        assert(arr.spec_index(i) < target);
    }
}

}