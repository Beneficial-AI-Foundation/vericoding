// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper for checking evenness */
spec fn mod2_eq_zero(n: int) -> bool { n % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return boolean expression for evenness without runtime int casts */
    n % 2 == 0
}
// </vc-code>

}
fn main() {}