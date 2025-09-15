// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed as the `is_even` function directly implements the logic. */
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Direct modulo check. */
{
    n % 2 == 0
}
// </vc-code>

}
fn main() {}