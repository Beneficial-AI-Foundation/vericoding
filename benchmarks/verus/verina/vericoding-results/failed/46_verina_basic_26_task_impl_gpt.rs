// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove invalid numeric suffixes and provide a spec helper */
spec fn is_even_spec(n: int) -> bool {
    n % 2 == 0
}

// </vc-helpers>

// <vc-spec>
fn is_even(n: int) -> (result: bool)
    ensures
        result <==> (n % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return boolean expression using int literals without suffixes */
    n % 2 == 0
}
// </vc-code>

}
fn main() {}