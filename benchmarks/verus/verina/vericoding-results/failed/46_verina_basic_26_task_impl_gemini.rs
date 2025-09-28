// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): defined spec constants for literals */
spec const TWO: int = 2;
spec const ZERO: int = 0;
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used spec constants to fix type inference error */
    n % TWO == ZERO
}
// </vc-code>

}
fn main() {}