// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added a trigger to the forall quantifier */
spec fn all_consecutive_until(s: Seq<i32>, n: int) -> bool
{
    forall|i: int| 0 <= i < n ==> i + 1 < s.len() && #[trigger] s@[i+1] == s@[i] + 1
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
    /* code modified by LLM (iteration 4): added a trigger to the loop invariant's forall quantifier */
    let mut i: usize = 0;
    while i < arr.len() - 1
        invariant
            arr.len() > 0,
            0 <= i < arr.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] arr.view()@[k+1] == arr.view()@[k] + 1
        decreases arr.len() - 1 - i
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