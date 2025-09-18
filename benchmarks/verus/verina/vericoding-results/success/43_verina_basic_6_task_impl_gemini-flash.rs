// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a < b {
        a
    } else {
        b
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
    let min_ab = min(a, b);
    min(min_ab, c)
}
// </vc-code>

}
fn main() {}