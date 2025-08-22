use vstd::prelude::*;

fn main() {}

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        /* code modified by LLM (iteration 2): Added trigger annotation to fix quantifier trigger inference error */
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    /* code modified by LLM (iteration 1): Fixed loop bounds, invariant, and array access bounds checking */
    for idx in 0..arr.len() - 1
        invariant
            arr.len() > 0,
            /* code modified by LLM (iteration 2): Added trigger annotation to fix quantifier trigger inference error */
            forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
            forall|i: int, j: int|
                0 <= i < j < arr.len() && j == i + 1 && j <= idx ==> (arr[i] + 1 == arr[j]),
    {
        /* code modified by LLM (iteration 1): Added bounds checking and proper indexing */
        assert(idx < arr.len() - 1);
        assert(idx + 1 < arr.len());
        assert(0 <= arr[idx as int] + 1 < i32::MAX);
        
        if arr[idx] + 1 != arr[idx + 1] {
            return false;
        }
    }
    return true;
}

} // verus!