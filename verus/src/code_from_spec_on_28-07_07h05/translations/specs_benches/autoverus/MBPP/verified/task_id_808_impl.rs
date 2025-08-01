use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
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