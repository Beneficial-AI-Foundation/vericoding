// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_i32(x: i32, y: i32) -> (r: i32)
    ensures
        r >= x && r >= y,
        r == x || r == y
{
    if x >= y { x } else { y }
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
    if a >= b {
        if a >= c {
            a
        } else {
            c
        }
    } else {
        if b >= c {
            b
        } else {
            c
        }
    }
}
// </vc-code>

}
fn main() {}