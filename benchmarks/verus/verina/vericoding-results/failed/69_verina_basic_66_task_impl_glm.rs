// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_even_spec(x: int) -> bool /* helper modified by LLM (iteration 4): define spec function for evenness */ {
    (x % 2) == 0
}
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): call spec function to compute result */
    is_even_spec(x)
}
// </vc-code>

}
fn main() {}