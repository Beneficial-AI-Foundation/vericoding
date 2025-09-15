// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_i32(a: i32, b: i32) -> (r: i32)
    ensures
        r <= a && r <= b,
        r == a || r == b
{
    if a <= b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn my_min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
// </vc-spec>
// <vc-code>
{
    let r = min_i32(a, b);
    r
}
// </vc-code>

}
fn main() {}