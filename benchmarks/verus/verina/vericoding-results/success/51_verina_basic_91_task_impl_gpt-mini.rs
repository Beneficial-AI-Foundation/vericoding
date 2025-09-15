// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mk_swap(a: i32, b: i32) -> (i32, i32) { (b, a) }
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
    let res: (i32, i32) = (y, x);
    res
}
// </vc-code>

}
fn main() {}