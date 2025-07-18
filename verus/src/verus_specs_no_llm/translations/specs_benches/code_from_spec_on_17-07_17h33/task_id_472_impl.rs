use vstd::prelude::*;

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut idx = 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant to use correct bounds and added proper range checking */
    while idx < arr.len() - 1
        invariant
            0 <= idx <= arr.len() - 1,
            forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 && j <= idx ==> (arr[i] + 1 == arr[j]),
        decreases arr.len() - idx
    {
        /* code modified by LLM (iteration 4): use precondition to ensure safe arithmetic and check consecutive property */
        assert(0 <= arr[idx] + 1 < i32::MAX); // follows from precondition
        if arr[idx] + 1 != arr[idx + 1] {
            return false;
        }
        idx += 1;
    }
    
    return true;
}

} // verus!

fn main() {}