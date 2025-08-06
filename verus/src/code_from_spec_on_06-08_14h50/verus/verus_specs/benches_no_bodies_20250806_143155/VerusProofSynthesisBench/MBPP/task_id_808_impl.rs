use vstd::prelude::*;

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
    // post-conditions-end
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != k,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases arr.len() - i
    {
        if arr[i] == k {
            return true;
        }
        i += 1;
    }
    false
}

} // verus!

fn main() {}