use vstd::prelude::*;


verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] != k,
        decreases arr.len() - i,
    {
        if arr[i] == k {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

} // verus!

fn main() {}