use vstd::prelude::*;


verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr@[i] == k)),
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr@[j] != k,
    {
        if arr@[i] == k {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

} // verus!

fn main() {}