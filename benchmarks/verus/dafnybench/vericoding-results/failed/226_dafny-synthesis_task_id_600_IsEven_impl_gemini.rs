// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures result <==> n % 2 == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The compiler errors pointed at the explicit `as int` casts, not the use of `n`. Removing the casts. */
{
    n % 2 == 0
}
// </vc-code>

}
fn main() {}