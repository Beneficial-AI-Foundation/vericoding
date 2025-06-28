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
            // result is either -1 or a valid index in the processed part
            result == -1 || (0 <= result < i && arr.spec_index(result) == elem),
            // if result is -1, no element found in processed part
            result == -1 ==> (forall|j: int| 0 <= j < i ==> arr.spec_index(j) != elem),
            // if result is not -1, it's the last occurrence in processed part
            result != -1 ==> (forall|j: int| result < j < i ==> arr.spec_index(j) != elem),
            // Key invariant: result is the rightmost occurrence in [0, i)
            result != -1 ==> (forall|j: int| 0 <= j < i && arr.spec_index(j) == elem ==> j <= result),
    {
        if arr[i] == elem {
            result = i as int;
        }
        i += 1;
    }
    
    // After the loop, i == arr.len()
    assert(i as int == arr.len());
    
    // Prove the postconditions
    if result != -1 {
        // We know result is the last occurrence in the entire array
        assert(0 <= result < arr.len());
        assert(arr.spec_index(result) == elem);
        assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
        
        // Prove the condition about the next element
        if result < arr.len() - 1 {
            let next_idx = result + 1;
            assert(0 <= next_idx < arr.len());
            assert(result < next_idx);
            // Since array is sorted and next element is not elem (but elem <= next)
            // we can conclude next > elem
            assert(arr.spec_index(next_idx) != elem) by {
                assert(result < next_idx < arr.len());
                assert(forall|j: int| result < j < arr.len() ==> arr.spec_index(j) != elem);
            };
            assert(arr.spec_index(result) <= arr.spec_index(next_idx)) by {
                assert(0 <= result < next_idx < arr.len());
                assert(forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr.spec_index(i) <= arr.spec_index(j));
            };
            assert(arr.spec_index(next_idx) >= elem) by {
                assert(arr.spec_index(result) == elem);
                assert(arr.spec_index(result) <= arr.spec_index(next_idx));
            };
            // Since next_idx != elem and next_idx >= elem, we have next_idx > elem
            assert(arr.spec_index(next_idx) > elem) by {
                assert(arr.spec_index(next_idx) != elem);
                assert(arr.spec_index(next_idx) >= elem);
            };
        }
        
        // Final assertion for the postcondition
        assert(pos == result ==> (pos == arr.len() - 1 || arr.spec_index(pos + 1) > elem)) by {
            if result == arr.len() - 1 {
                // trivially true
            } else {
                assert(result < arr.len() - 1);
                assert(arr.spec_index(result + 1) > elem);
            }
        };
    } else {
        // No element found in entire array
        assert(forall|j: int| 0 <= j < arr.len() ==> arr.spec_index(j) != elem) by {
            assert(result == -1);
            assert(forall|j: int| 0 <= j < i ==> arr.spec_index(j) != elem);
            assert(i as int == arr.len());
        };
    }
    
    result
}

}