// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add trigger on array term to help quantifier instantiation */
spec fn adj_eq_up_to(arr: &Vec<i32>, n: nat) -> bool {
    forall|i: int| 0 <= i && i + 1 < n ==> #[trigger] arr@[i] + 1 == arr@[i+1]
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
    /* code modified by LLM (iteration 5): iterate and maintain adj_eq_up_to invariant with trigger-fixed helper */
    let n: usize = arr.len();
    if n <= 1 { return true; }
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i && i <= n,
            adj_eq_up_to(arr, i as nat),
        decreases
            n - i
    {
        let prev: i32 = arr[i - 1];
        let cur: i32 = arr[i];
        if prev + 1 != cur {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}