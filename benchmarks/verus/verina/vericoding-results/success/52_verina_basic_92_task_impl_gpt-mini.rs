// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn swap_property(x: i32, y: i32, r: (i32, i32)) ensures r.0 == y && r.1 == x ==> (x != y ==> r.0 != x && r.1 != y) { }
// </vc-helpers>

// <vc-spec>
fn swap_arithmetic(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> (result.0 != x && result.1 != y),
// </vc-spec>
// <vc-code>
{
    let result = (y, x);
    result
}
// </vc-code>

}
fn main() {}