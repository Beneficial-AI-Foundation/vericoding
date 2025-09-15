// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_two(x: i32, y: i32) -> (result: i32)
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
{
    let min_ab = min_two(a, b);
    let result = min_two(min_ab, c);
    result
}
// </vc-code>

}
fn main() {}