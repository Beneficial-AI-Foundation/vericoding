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
    /* code modified by LLM (iteration 2): use wrapping arithmetic to avoid overflow */
    let a = x.wrapping_add(y);
    let b = a.wrapping_sub(y);
    let c = a.wrapping_sub(b);
    (c, b)
}
// </vc-code>

}
fn main() {}