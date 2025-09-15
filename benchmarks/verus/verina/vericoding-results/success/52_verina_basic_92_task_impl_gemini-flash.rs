// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swap_arithmetic(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> (result.0 != x && result.1 != y),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [fixed overflow/underflow issues by using temporary variables and ensuring intermediate steps stay within i32 bounds if possible, or by reordering, but since regular 3-op swap is prone to over/underflow with i32, direct assignment is used to meet the function spec and avoid such issues. ] */
    let new_x = y;
    let new_y = x;
    (new_x, new_y)
}
// </vc-code>

}
fn main() {}