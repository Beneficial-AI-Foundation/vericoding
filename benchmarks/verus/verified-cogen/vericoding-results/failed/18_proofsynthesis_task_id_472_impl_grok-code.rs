// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added spec function for consecutive pair check to enable triggering in invariants. */
spec fn is_consecutive_pair(a: i32, b: i32) -> bool {
    a + 1 == b
}
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
    /* code modified by LLM (iteration 5): Updated invariant to use helper spec function as trigger instead of direct equality expression, resolving the trigger error. */
    let n = arr.len();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall |k: int| 0 <= k < i ==> #[trigger] is_consecutive_pair(arr@[k], arr@[k + 1]),
        decreases (n - 1 - i) as nat
    {
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}