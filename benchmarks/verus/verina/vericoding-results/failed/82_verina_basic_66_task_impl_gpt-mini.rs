// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define is_even as spec predicate stating existence of integer k with x == k + k */
spec fn is_even(x: int) -> bool { exists k: int :: x == k + k }
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result using integer modulus and return whether x is divisible by 2 */
    let result: bool = (x % 2) == 0;
    result
}
// </vc-code>

}
fn main() {}