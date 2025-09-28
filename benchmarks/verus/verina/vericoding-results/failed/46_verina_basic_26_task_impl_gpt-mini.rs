// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper returning true iff n is even */
spec fn is_even_helper(n: int) -> bool { n % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return spec helper result */
    let result = is_even_helper(n);
    result
}
// </vc-code>

}
fn main() {}