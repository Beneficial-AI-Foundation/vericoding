// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn swap_spec(x: int, y: int) -> (result: (int, int))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y
{
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
    /* code modified by LLM (iteration 2): Fixed type mismatch by using executable code instead of proof */
    (y, x)
}
// </vc-code>

}
fn main() {}