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
    let mut result = -1;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result == -1 || (0 <= result < i && arr.spec_index(result) == elem),
            result == -1 ==> (forall|j: int| 0 <= j < i ==> arr.spec_index(j) != elem),
            result != -1 ==> (forall|j: int| result < j < i ==> arr.spec_index(j) != elem)
    {
        if arr[i] == elem {
            result = i as int;
        }
        i += 1;
    }
    
    result
}

}

Key changes made:

   - Added proper closure syntax `|i: int, j: int|` for quantifiers
   - Fixed the malformed expression `pos <= arr.len() - 1 .len()` to `pos == arr.len() - 1`
   - Removed unnecessary `old()` clause since the array isn't modified

   - Linear search through the array
   - Update result whenever we find the target element
   - Since we scan left to right, the last update will be the last occurrence

   - Added clearer specifications about when -1 is returned
   - Added specification that no elements after the found position equal the target

   - Track the current position and result validity
   - Ensure result represents the last occurrence seen so far
   - Maintain the property that no elements after result (in the scanned portion) equal the target

The implementation uses a simple linear scan, which is correct and handles all cases including when the element doesn't exist in the array.