// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added helper functions for checked arithmetic operations */
spec fn can_add(x: i32, y: i32) -> bool {
    x <= i32::MAX - y && x >= i32::MIN - y
}

spec fn can_sub(x: i32, y: i32) -> bool {
    x >= i32::MIN + y && x <= i32::MAX + y
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
    /* code modified by LLM (iteration 3): removed misplaced requires clause from function body */
    let sum = x + y;
    let diff = x - y;
    (sum, diff)
}
// </vc-code>

}
fn main() {}