// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove invalid integer suffixes and define evenness predicate */
spec fn is_even_int(x: int) -> bool { (x % 2) == 0 }
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (result: bool)
    ensures
        result == true <==> #[trigger] (x % 2) == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute evenness without invalid numeric suffixes */
    let result = (x % 2) == 0;
    return result;
}
// </vc-code>

}
fn main() {}