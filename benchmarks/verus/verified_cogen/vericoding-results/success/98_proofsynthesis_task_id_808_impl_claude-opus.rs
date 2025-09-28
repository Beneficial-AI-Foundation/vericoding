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
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] != k,
        decreases arr.len() - i,
    {
        if arr[i] == k {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}