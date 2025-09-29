// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed ensures on spec fn to satisfy Verus rule */
spec fn swap_pair(x: i32, y: i32) -> (i32, i32) {
    (y, x)
}
// </vc-helpers>

// <vc-spec>
fn swap_simultaneous(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return swapped tuple directly to satisfy ensures */
    (y, x)
}
// </vc-code>

}
fn main() {}