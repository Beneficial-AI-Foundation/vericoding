// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_of_two(x: i32, y: i32) -> (result: i32)
    ensures
        result <= x && result <= y,
        result == x || result == y
{
    if x <= y {
        x
    } else {
        y
    }
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
    let ab_min = min_of_two(a, b);
    let result = min_of_two(ab_min, c);
    result
}
// </vc-code>

}
fn main() {}