// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiple_returns(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == x + y,
        result.1 + y == x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Return correct values satisfying postconditions */
    (x + y, x - y)
}
// </vc-code>

}
fn main() {}