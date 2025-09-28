// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed invalid int suffix and kept simple parity predicate */
spec fn is_even_int(x: int) -> bool {
    (x % 2) == 0
}
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove invalid int suffix and compute parity directly */
    let result: bool = (x % 2) == 0;
    result
}
// </vc-code>

}
fn main() {}