// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute pair (x + y, x - y) using standard arithmetic */
fn make_result(x: i32, y: i32) -> (i32, i32) {
    (x + y, x - y)
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
    /* code modified by LLM (iteration 5): compute and return pair ensuring postconditions */
    let r = make_result(x, y);
    r
}
// </vc-code>

}
fn main() {}