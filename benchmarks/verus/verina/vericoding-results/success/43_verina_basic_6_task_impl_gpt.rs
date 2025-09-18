// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_i32(a: i32, b: i32) -> (res: i32)
    ensures
        res <= a && res <= b,
        res == a || res == b
{
    if a <= b { a } else { b }
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
    let m = min_i32(a, b);
    let r = min_i32(m, c);
    r
}
// </vc-code>

}
fn main() {}