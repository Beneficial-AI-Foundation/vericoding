use vstd::prelude::*;


verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
    // post-conditions-end
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < arr.len()
        invariant
            forall|i: int| 0 <= i < idx ==> arr[i] != k,
        decreases arr.len() - idx,
    {
        if arr[idx] == k {
            return true;
        }
        idx += 1;
    }
    false
}

} // verus!

fn main() {}