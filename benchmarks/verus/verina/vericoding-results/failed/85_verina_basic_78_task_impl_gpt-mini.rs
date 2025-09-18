// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use wrapping arithmetic to avoid overflow */
fn make_pair(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
{
    let r0: i32 = x.wrapping_add(y);
    let r1: i32 = x.wrapping_sub(y);
    (r0, r1)
}
// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build and return pair using helper with wrapping ops */
    let result: (i32, i32) = make_pair(x, y);
    result
}
// </vc-code>

}
fn main() {}