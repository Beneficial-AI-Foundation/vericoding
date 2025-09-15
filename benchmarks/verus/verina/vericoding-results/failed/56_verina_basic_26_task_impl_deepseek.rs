// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_even_spec(n: int) -> bool {
    n % 2 == 0
}

proof fn even_zero() 
    ensures 
        is_even_spec(0)
{
}

proof fn even_step(n: int)
    requires
        n >= 0,
    ensures
        is_even_spec(n) <==> is_even_spec(n + 2)
{
}
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix integer literal vs int type mismatch */
{
    if n == 0int {
        true
    } else if n < 0int {
        is_even(-n)
    } else {
        !is_even(n - 1int)
    }
}
// </vc-code>

}
fn main() {}