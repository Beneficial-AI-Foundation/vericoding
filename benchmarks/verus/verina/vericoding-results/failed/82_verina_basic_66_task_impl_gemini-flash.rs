// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch error by explicitly casting integer literals to `int` for the comparison. */
{
    if x % 2 == (0_int) {
        true
    } else {
        false
    }
}
// </vc-code>

}
fn main() {}