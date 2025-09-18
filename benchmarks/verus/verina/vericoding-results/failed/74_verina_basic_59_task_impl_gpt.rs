// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn double(a: int) -> int { 2 * a }
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    let d = x + x;
    let q = d + d;
    (d, q)
}
// </vc-code>

}
fn main() {}