use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr@[j] == element,
        decreases arr.len() - i
    {
        if arr[i] != element {
            return false;
        }
        i = i + 1;
    }
    true
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}