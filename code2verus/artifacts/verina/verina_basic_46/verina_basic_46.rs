use vstd::prelude::*;

verus! {

// Precondition: array is sorted (non-decreasing)
spec fn last_position_precond(arr: &Vec<i32>, elem: i32) -> bool {
    // List.Pairwise (· ≤ ·) arr.toList
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

// Check if all elements in slice are not equal to elem
spec fn all_not_equal(arr: &Vec<i32>, start: int, end: int, elem: i32) -> bool {
    forall|k: int| start <= k < end ==> arr[k] != elem
}

// Postcondition specification
spec fn last_position_postcond(arr: &Vec<i32>, elem: i32, result: i32) -> bool {
    (result >= 0 ==> 
        result < arr.len() &&
        arr[result as int] == elem &&
        all_not_equal(arr, result as int + 1, arr.len() as int, elem)
    ) &&
    (result == -1 ==> all_not_equal(arr, 0, arr.len() as int, elem))
}

fn last_position(arr: &Vec<i32>, elem: i32) -> (result: i32)
    requires 
        last_position_precond(arr, elem),
        arr.len() < 0x8000_0000, // ensure i32 conversion is safe
    ensures 
        last_position_postcond(arr, elem, result)
{
    let mut i: usize = 0;
    let mut pos: i32 = -1;
    
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            i <= arr.len() < 0x8000_0000,
            pos >= 0 ==> (0 <= pos < arr.len() && arr[pos as int] == elem),
            forall|j: int| 0 <= j < i && arr[j] == elem ==> j <= pos,
            pos == -1 <==> forall|j: int| 0 <= j < i ==> arr[j] != elem,
        decreases arr.len() - i
    {
        if arr[i] == elem {
            assert(i < arr.len() < 0x8000_0000);
            pos = i as i32;
            assert(pos as int == i);
        }
        i += 1;
    }
    
    pos
}

fn main() {}

} // verus!