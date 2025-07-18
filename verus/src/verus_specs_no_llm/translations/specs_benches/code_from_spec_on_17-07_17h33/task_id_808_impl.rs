use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 1): fixed function structure by placing ensures clause in correct position */
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    /* code modified by LLM (iteration 1): implemented function body with proper loop invariant */
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != k,
    {
        if arr[i] == k {
            return true;
        }
    }
    false
}

} // verus!

fn main() {}