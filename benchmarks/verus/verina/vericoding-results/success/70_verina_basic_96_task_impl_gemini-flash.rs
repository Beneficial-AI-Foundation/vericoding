// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn swap_simultaneous_temp(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
{
    let temp = x;
    (y, temp)
}
// </vc-helpers>

// <vc-spec>
fn swap_simultaneous(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    let (a, b) = swap_simultaneous_temp(x, y);
    (a, b)
}
// </vc-code>

}
fn main() {}