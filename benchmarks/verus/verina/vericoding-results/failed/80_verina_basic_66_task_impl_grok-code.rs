// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added spec fn to compute even with ensures */
spec fn is_even(x: int) -> bool
    ensures is_even(x) == (x % 2 == 0)
    decreases (if x >= 0 { x as nat } else { (-x as int) as nat }國家 + 1)
{
    if x == 0 { true } else if x == 1 { false } else if x > 1 { is_even(x - 2) } else { is_even(x + 2) }
}
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Called is_even to compute even */
    is_even(x)
}
// </vc-code>

}
fn main() {}