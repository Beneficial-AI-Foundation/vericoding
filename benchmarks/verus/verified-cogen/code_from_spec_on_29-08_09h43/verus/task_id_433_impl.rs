use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> number > arr[j],
        decreases arr.len() - i,
    {
        if number <= arr[i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

} // verus!

fn main() {}