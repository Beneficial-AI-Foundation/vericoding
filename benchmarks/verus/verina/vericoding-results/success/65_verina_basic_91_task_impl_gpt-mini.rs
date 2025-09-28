// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): swap specification */
spec fn swap_spec(x: i32, y: i32) -> (i32, i32) {
    (y, x)
}
// </vc-helpers>

// <vc-spec>
fn swap(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return swapped tuple */
    (y, x)
}
// </vc-code>

}
fn main() {}