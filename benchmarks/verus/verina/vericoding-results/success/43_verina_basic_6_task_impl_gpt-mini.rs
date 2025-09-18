// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): min2 returns the smaller of two integers with named result */
fn min2(x: i32, y: i32) -> (result: i32)
    ensures
        result <= x && result <= y,
        result == x || result == y,
{
    if x <= y { x } else { y }
}

// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result <= a && result <= b && result <= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): compute min of three by composing min2 helper */
{
    let t = min2(a, b);
    let r = min2(t, c);
    r
}

// </vc-code>

}
fn main() {}