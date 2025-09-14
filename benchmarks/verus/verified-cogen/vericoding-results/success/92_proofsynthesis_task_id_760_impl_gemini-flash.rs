// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed unnecessary helper function, the specification itself is clear enough */
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)

    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added decreases clause to the loop */
{
    if arr.len() <= 1 {
        true
    } else {
        let mut i = 1;
        while i < arr.len()
            invariant
                1 <= i <= arr.len(),
                forall|j: int| 1 <= j < i ==> arr[0] == #[trigger] arr[j],
            decreases arr.len() - i,
        {
            if arr[0] != arr[i] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-code>

}
fn main() {}