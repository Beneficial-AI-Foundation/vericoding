// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): name return and prove swap of pair */
fn swap_pair(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
{
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
    /* code modified by LLM (iteration 2): call helper to swap and return result */
    let result = swap_pair(x, y);
    result
}
// </vc-code>

}
fn main() {}