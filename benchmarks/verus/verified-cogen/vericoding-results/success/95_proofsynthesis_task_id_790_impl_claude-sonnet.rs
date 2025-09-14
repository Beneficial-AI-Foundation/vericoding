// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_even_at_even_indices(arr: &Vec<usize>) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2))
}
// </vc-helpers>

// <vc-spec>
fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)),
        decreases arr.len() - index
    {
        if (index % 2) != (arr[index] % 2) {
            return false;
        }
        index += 1;
    }
    true
}
// </vc-code>

}
fn main() {}