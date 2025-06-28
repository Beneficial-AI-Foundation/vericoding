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
    
    // After the loop, establish the postconditions
    if result != -1 {
        // We know result is a valid index with the target element
        assert(0 <= result < arr.len());
        assert(arr.spec_index(result) == elem);
        
        // Prove that all elements after result are not equal to elem
        assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
        
        // If result is not the last element, prove the next element is greater
        if result < arr.len() - 1 {
            let next = result + 1;
            assert(result < next < arr.len());
            
            // From sortedness: arr[result] <= arr[next]
            assert(arr.spec_index(result) <= arr.spec_index(next));
            
            // From loop invariant: arr[next] != elem
            assert(arr.spec_index(next) != elem);
            
            // Since arr[result] == elem and arr[next] >= elem and arr[next] != elem
            // Therefore arr[next] > elem
            assert(arr.spec_index(result) == elem);
            assert(arr.spec_index(next) >= elem);
            assert(arr.spec_index(next) != elem);
            assert(arr.spec_index(next) > elem);
        }
    } else {
        // result == -1 means no element was found
        assert(forall|j: int| 0 <= j < arr.len() ==> arr.spec_index(j) != elem);
    }
    
    result
}

}