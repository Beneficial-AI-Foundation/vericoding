// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn swap_helper(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y {
    (y, x)
}
// </vc-helpers>

// <vc-spec>
fn swap(x: i32, y: i32) -> (result: (i32, i32))
    ensures
        result.0 == y,
        result.1 == x,
        x != y ==> result.0 != x && result.1 != y,
// </vc-spec>
// <vc-code>
{
    let temp = x;
    let result = (y, temp);
    result
}
// </vc-code>

}
fn main() {}