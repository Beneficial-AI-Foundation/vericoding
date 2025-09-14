// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < (i as int) ==> (arr@[j] == element),
        decreases arr.len() - i
    {
        if arr[i] != element {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}