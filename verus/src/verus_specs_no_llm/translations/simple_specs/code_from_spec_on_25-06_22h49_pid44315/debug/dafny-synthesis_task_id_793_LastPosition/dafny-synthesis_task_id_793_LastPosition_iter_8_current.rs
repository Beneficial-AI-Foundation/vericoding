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
            // Keep the sorted property
            forall|x: int, y: int| 0 <= x < y < arr.len() ==> arr.spec_index(x) <= arr.spec_index(y),
    {
        if arr.spec_index(i) == elem {
            result = i;
        }
        i += 1;
    }
    
    // Proof block to establish postconditions
    proof {
        if result != -1 {
            // Establish that result is in bounds and has the right value
            assert(0 <= result < arr.len());
            assert(arr.spec_index(result) == elem);
            
            // Prove no elements after result equal elem
            assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
            
            // If result is not the last index, prove next element is greater
            if result < arr.len() - 1 {
                let next_idx = result + 1;
                assert(0 <= result < next_idx < arr.len());
                // From sortedness
                assert(arr.spec_index(result) <= arr.spec_index(next_idx));
                // From our finding that no elem after result
                assert(arr.spec_index(next_idx) != elem);
                // Since arr[result] == elem and arr[next] >= elem and arr[next] != elem
                assert(arr.spec_index(result) == elem);
                assert(arr.spec_index(next_idx) >= arr.spec_index(result));
                assert(arr.spec_index(next_idx) >= elem);
                assert(arr.spec_index(next_idx) != elem);
                // Therefore arr[next] > elem
                assert(arr.spec_index(next_idx) > elem);
            }
            
            // Additional proof to help verification
            assert(result == arr.len() - 1 || arr.spec_index(result + 1) > elem);
        } else {
            // result == -1, so no element was found
            assert(forall|j: int| 0 <= j < arr.len() ==> arr.spec_index(j) != elem);
        }
        
        // Prove the main postcondition structure
        if result == -1 {
            assert(forall|i: int| 0 <= i < arr.len() ==> arr.spec_index(i) != elem);
        } else {
            assert(0 <= result < arr.len());
            assert(arr.spec_index(result) == elem);
            assert(result == arr.len() - 1 || arr.spec_index(result + 1) > elem);
            assert(forall|i: int| result < i < arr.len() ==> arr.spec_index(i) != elem);
        }
    }
    
    result
}

}