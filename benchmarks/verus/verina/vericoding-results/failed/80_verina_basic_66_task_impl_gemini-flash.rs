// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type to `int` for `%` operator and operand. */
fn is_even_def(x: int) -> bool {
    x % 2i == 0i
}
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type to `int` for `%` operator and operand. */
{
    x % 2i == 0i
}
// </vc-code>

}
fn main() {}