// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_two(x: i32, y: i32) -> (m: i32)
    ensures
        m <= x && m <= y,
        m == x || m == y,
{
    if x <= y {
        x
    } else {
        y
    }
}
// </vc-helpers>

// <vc-spec>
fn min_of_three(a: i32, b: i32, c: i32) -> (min: i32)
    ensures
        min <= a && min <= b && min <= c,
        (min == a) || (min == b) || (min == c),
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