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
    {
        if arr.spec_index(i) == elem {
            result = i;
        }
        i += 1;
    }
    
    // After the loop, establish postconditions
    if result != -1 {
        // Prove that result satisfies the next element condition
        if result < arr.len() - 1 {
            // Use the sorted property and the fact that no elem found after result
            assert(arr.spec_index(result) <= arr.spec_index(result + 1));
            assert(arr.spec_index(result + 1) != elem);
            assert(arr.spec_index(result + 1) >= elem);
            assert(arr.spec_index(result + 1) > elem);
        }
    }
    
    result
}

}