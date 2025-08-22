use vstd::prelude::*;

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
    // post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 3): use usize for array indexing in executable code */
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l <= i && l == k + 1 ==> (arr[k] + 1 == arr[l]),
        decreases arr.len() - 1 - i,
    {
        /* code modified by LLM (iteration 3): use usize indexing and add ghost assertions for verification */
        assert(0 <= i < arr.len() - 1);
        assert(0 <= i + 1 < arr.len());
        assert(0 <= arr[i as int] + 1 < i32::MAX);
        
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        i += 1;
    }
    return true;
}

} // verus!

fn main() {}