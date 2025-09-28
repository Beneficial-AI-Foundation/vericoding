// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added loop invariant to prove postcondition */
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr@[j] != k
    {
        if arr[i] == k {
            return true;
        }
    }
    false
}
// </vc-code>

}
fn main() {}