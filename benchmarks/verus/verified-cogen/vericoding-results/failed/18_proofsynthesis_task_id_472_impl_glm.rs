// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Added trigger annotation to quantifier in invariant */
    let mut i: usize = 0;
    while i < arr.len() - 1
        invariant
            i <= arr.len() - 1,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] arr@[k] + 1 == arr@[k+1])
        decreases (arr.len() as int - 1) - (i as int)
    {
        if arr[i] + 1 != arr[i+1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}