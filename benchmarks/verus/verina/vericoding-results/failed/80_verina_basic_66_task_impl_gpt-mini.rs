// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): check parity using modulo */
fn is_even(x: int) -> bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute parity using helper is_even */
    let result = is_even(x);
    result
}
// </vc-code>

}
fn main() {}