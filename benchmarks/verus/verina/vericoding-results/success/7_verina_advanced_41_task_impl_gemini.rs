// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_of_two(a: i32, b: i32) -> (result: i32)
    ensures
        result >= a && result >= b,
        result == a || result == b
{
    if a >= b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn max_of_three(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
// </vc-spec>
// <vc-code>
{
    let max_ab = max_of_two(a, b);
    let result = max_of_two(max_ab, c);
    result
}
// </vc-code>

}
fn main() {}