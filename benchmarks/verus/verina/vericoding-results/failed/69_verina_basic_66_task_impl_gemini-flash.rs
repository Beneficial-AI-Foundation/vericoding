// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section is empty because no helper functions are needed for this problem. */

// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch issues by casting `x` to `int` before using the modulo operator. */
{
    ((x as int) % (2 as int)) == (0 as int)
}
// </vc-code>

}
fn main() {}