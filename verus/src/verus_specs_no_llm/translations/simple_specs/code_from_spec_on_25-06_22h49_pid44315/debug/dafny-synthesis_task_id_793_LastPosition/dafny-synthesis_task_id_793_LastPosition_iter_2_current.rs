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
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result == -1 || (0 <= result < i && arr.spec_index(result) == elem),
            result == -1 ==> (forall|j: int| 0 <= j < i ==> arr.spec_index(j) != elem),
            result != -1 ==> (forall|j: int| result < j < i ==> arr.spec_index(j) != elem),
            // Additional invariant to help with the sorted property
            result != -1 ==> (forall|j: int| 0 <= j < result ==> arr.spec_index(j) <= elem),
    {
        if arr[i] == elem {
            result = i as int;
        }
        i += 1;
    }
    
    // Proof assertions to help verification
    assert(i == arr.len());
    
    if result != -1 {
        // Use the sorted property to prove the postcondition
        assert(arr.spec_index(result) == elem);
        if result < arr.len() - 1 {
            // Since array is sorted and we found the last occurrence,
            // the next element must be greater
            assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
            // By sortedness, if next element exists and current equals elem,
            // then next element must be > elem (since we found last occurrence)
            let next_idx = result + 1;
            assert(next_idx < arr.len());
            assert(arr.spec_index(result) <= arr.spec_index(next_idx));
            assert(arr.spec_index(next_idx) != elem);
            assert(arr.spec_index(next_idx) > elem);
        }
    }
    
    result
}

}