use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 1): Fixed specification to properly check that all elements before index are even */
spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& (forall|k: int| 0 <= k < idx ==> (arr[k] % 2 == 0))
        &&& arr[idx as int] % 2 != 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}

/* code modified by LLM (iteration 1): Added assertion to help prove postcondition */
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures check_find_first_odd(arr, index),
{
    for i in 0..arr.len()
        invariant forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0)
    {
        if arr[i] % 2 != 0 {
            assert(forall|k: int| 0 <= k < i ==> (arr[k] % 2 == 0));
            assert(arr[i as int] % 2 != 0);
            return Some(i);
        }
    }
    None
}

} // verus!

fn main() {}