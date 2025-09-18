// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper is correct but was called from an exec context */
spec fn is_even(v: int) -> bool { v % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced invalid spec function call with direct executable check using the modulo operator */
    x % 2 == 0
}
// </vc-code>

}
fn main() {}