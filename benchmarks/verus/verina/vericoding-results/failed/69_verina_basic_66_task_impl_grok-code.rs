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
{
/* code modified by LLM (iteration 5): Removed invalid 'int' suffixes on integer literals to fix compilation error */
    (x % 2 == 0)
}
// </vc-code>

}
fn main() {}