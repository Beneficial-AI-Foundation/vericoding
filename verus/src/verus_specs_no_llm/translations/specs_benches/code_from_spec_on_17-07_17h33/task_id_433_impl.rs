use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 1): Fixed function signature structure - moved ensures clause to correct position after function signature */
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    /* code modified by LLM (iteration 1): Removed unreachable return statement and fixed loop invariant bounds */
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> number > arr[j],
    {
        if number <= arr[i] {
            return false;
        }
    }
    true
}

} // verus!

fn main() {}