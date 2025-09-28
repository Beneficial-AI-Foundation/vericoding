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
    let mut a = x;
    let mut b = y;

    a = a.wrapping_add(b);
    b = a.wrapping_sub(b);
    a = a.wrapping_sub(b);

    (a, b)
}
// </vc-code>

}
fn main() {}