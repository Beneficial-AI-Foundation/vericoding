use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> ((j % 2) == (arr@[j] % 2)),
    {
        if (i % 2) != (arr[i] % 2) {
            return false;
        }
    }
    true
}
// </vc-code>

} // verus!

fn main() {}