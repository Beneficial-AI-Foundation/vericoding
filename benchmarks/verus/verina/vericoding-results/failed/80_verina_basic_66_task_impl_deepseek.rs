// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

    /* helper modified by LLM (iteration 5): Remove unnecessary helper function */

// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix integer literal syntax */
    if x % 2 == 0 {
        true
    } else {
        false
    }
}
// </vc-code>

}
fn main() {}