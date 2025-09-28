// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `is_even` to use integer literals as `int` type. */
fn is_even_pred(n: int) -> bool {
    n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `is_even` to use integer literals as `int` type. */
{
    if n % 2 == 0 {
        true
    } else {
        false
    }
}
// </vc-code>

}
fn main() {}