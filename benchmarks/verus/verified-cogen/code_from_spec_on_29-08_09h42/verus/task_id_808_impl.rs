use vstd::prelude::*;


verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
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
// </vc-code>

} // verus!

fn main() {}