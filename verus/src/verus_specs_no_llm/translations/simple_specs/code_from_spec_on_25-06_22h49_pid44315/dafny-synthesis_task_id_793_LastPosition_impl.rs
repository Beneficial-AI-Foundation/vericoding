use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LastPosition(arr: Vec<int>, elem: int) -> (pos: int)
    requires
        arr.len() > 0,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr.spec_index(i) <= arr.spec_index(j)
    ensures
        pos == -1 || (0 <= pos < arr.len() && arr.spec_index(pos) == elem && 
                      (pos == arr.len() - 1 || arr.spec_index(pos + 1) > elem)),
        pos == -1 ==> (forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) != elem),
        pos != -1 ==> (forall|i: int| pos < i < arr.len() ==> arr.spec_index(i) != elem)
{
    let mut result: int = -1;
    let mut i: int = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result == -1 || (0 <= result < i && arr.spec_index(result) == elem),
            result == -1 ==> (forall|j: int| 0 <= j < i ==> arr.spec_index(j) != elem),
            result != -1 ==> (forall|j: int| result < j < i ==> arr.spec_index(j) != elem),
            result != -1 ==> (forall|j: int| 0 <= j < i && arr.spec_index(j) == elem ==> j <= result),
            forall|x: int, y: int| 0 <= x < y < arr.len() ==> arr.spec_index(x) <= arr.spec_index(y),
    {
        if arr.spec_index(i) == elem {
            result = i;
        }
        i += 1;
    }
    
    // Prove the postconditions
    if result != -1 {
        // We know result is a valid index with the target element
        assert(0 <= result < arr.len());
        assert(arr.spec_index(result) == elem);
        
        // From the loop invariant, we know that no element after result (up to i) equals elem
        // Since i == arr.len() after the loop, this means no element after result equals elem
        assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
        
        // If result is not the last element, we need to prove the next element is greater
        if result < arr.len() - 1 {
            let next_idx = result + 1;
            assert(result < next_idx < arr.len());
            
            // From the sortedness property
            assert(arr.spec_index(result) <= arr.spec_index(next_idx));
            
            // From our proven fact that no element after result equals elem
            assert(arr.spec_index(next_idx) != elem);
            
            // Since arr[result] == elem, arr[next_idx] >= elem, and arr[next_idx] != elem
            // we can conclude arr[next_idx] > elem
            assert(arr.spec_index(result) == elem);
            assert(arr.spec_index(next_idx) >= elem);
            assert(arr.spec_index(next_idx) != elem);
            
            // This assertion should now be provable
            assert(arr.spec_index(next_idx) > elem);
        }
        
        // Final assertion for the ensures clause
        assert(pos == result && result != -1);
        assert(0 <= result < arr.len() && arr.spec_index(result) == elem);
        if result < arr.len() - 1 {
            assert(arr.spec_index(result + 1) > elem);
        }
    } else {
        // result == -1 case
        // From loop invariant: no element in range [0, i) equals elem
        // Since i == arr.len() after loop, no element in the entire array equals elem
        assert(forall|j: int| 0 <= j < arr.len() ==> arr.spec_index(j) != elem);
    }
    
    result
}

}