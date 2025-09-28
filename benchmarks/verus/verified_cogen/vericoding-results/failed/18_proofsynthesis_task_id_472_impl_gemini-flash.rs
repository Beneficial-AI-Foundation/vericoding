// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a specification function for the problem statement. */
spec fn contains_consecutive_numbers_spec(arr: &Vec<i32>) -> bool { forall|i: int, j: int| 0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j]) }
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),

    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusting the loop termination condition and the invariant predicate to correctly reflect the problem. Correctly handling the empty array and single-element array cases at the start before the loop. */
{
    if arr.len() == 0 {
        return true;
    }
    if arr.len() == 1 {
        return true;
    }

    let mut i: usize = 0;
    while i < arr.len() - 1
        invariant
            0 <= i,
            i <= arr.len() - 1,
            arr.len() >= 1,
            forall|idx: int, jdx: int| 0 <= idx < jdx < (i as int) + 1 && jdx == idx + 1 ==> (arr[idx] + 1 == arr[jdx]),
        decreases arr.len() - 1 - i,
    {
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}