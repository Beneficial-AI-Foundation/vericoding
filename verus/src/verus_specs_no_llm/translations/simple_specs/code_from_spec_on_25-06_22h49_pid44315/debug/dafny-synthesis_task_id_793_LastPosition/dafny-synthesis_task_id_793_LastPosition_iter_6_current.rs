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
            // Additional invariant to help with the sorted property
            forall|x: int, y: int| 0 <= x < y < arr.len() ==> arr.spec_index(x) <= arr.spec_index(y),
    {
        if arr.spec_index(i) == elem {
            result = i;
        }
        i += 1;
    }
    
    // After the loop, we need to prove the postconditions
    if result != -1 {
        // We know result is the last occurrence in the array
        // because our invariant ensures no elem found after result
        assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
        
        // If result is not the last index, prove next element is greater
        if result < arr.len() - 1 {
            // From sortedness: arr[result] <= arr[result + 1]
            assert(arr.spec_index(result) <= arr.spec_index(result + 1));
            // From our invariant: arr[result + 1] != elem
            assert(arr.spec_index(result + 1) != elem);
            // Since arr[result] == elem and arr[result] <= arr[result + 1] and arr[result + 1] != elem
            // we must have arr[result + 1] > elem
            assert(arr.spec_index(result) == elem);
            assert(arr.spec_index(result + 1) >= elem);
            assert(arr.spec_index(result + 1) != elem);
            assert(arr.spec_index(result + 1) > elem);
        }
    }
    
    result
}

}