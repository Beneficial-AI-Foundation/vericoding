// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper returning parity */
spec fn is_even_def(x: int) -> bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call spec helper to compute parity */
    let result = is_even_def(x);
    result
}
// </vc-code>

}
fn main() {}