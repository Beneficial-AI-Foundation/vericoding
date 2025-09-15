// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn swap_pair(a: i32, b: i32) -> (result: (i32, i32))
    ensures
        result.0 == b,
        result.1 == a,
        a != b ==> result.0 != a && result.1 != b
{
    (b, a)
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
    let r = swap_pair(x, y);
    r
}
// </vc-code>

}
fn main() {}