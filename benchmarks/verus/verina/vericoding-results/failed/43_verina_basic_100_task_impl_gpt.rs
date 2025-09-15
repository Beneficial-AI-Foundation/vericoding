// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn triple_int(x: int) -> int { 3 * x }
proof fn triple_div_mul_identity(x: int)
    ensures
        triple_int(x) / 3 == x,
        (triple_int(x) / 3) * 3 == triple_int(x)
{ }
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    let result = x * 3;
    result
}
// </vc-code>

}
fn main() {}