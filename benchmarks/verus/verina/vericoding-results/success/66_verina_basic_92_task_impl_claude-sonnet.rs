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
    /* code modified by LLM (iteration 2): added overflow checks for arithmetic swap */
    if x.checked_add(y).is_none() {
        return (y, x);
    }
    let a = x + y;
    let b = a - y;
    let c = a - b;
    (c, b)
}
// </vc-code>

}
fn main() {}