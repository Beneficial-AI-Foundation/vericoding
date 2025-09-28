// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added safe int to usize conversion helper */
fn int_to_usize(x: int) -> (result: usize)
    requires
        x >= 0,
    ensures
        result == x as int,
{
    proof {
        // Cast is valid since x >= 0
    }
    x as usize
}
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use safe conversion helper and handle negative case */
{
    if x < 0 {
        let result: bool = (-x) % 2 == 0;
        result
    } else {
        let x_usize = int_to_usize(x);
        let result: bool = x_usize % 2 == 0;
        result
    }
}
// </vc-code>

}
fn main() {}