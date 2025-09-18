// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_multiple_of_three(n: i32) -> bool {
    n % 3 == 0
}

proof fn mul_3_div_3(x: i32)
    requires x >= i32::MIN / 3, x <= i32::MAX / 3
    ensures x * 3 / 3 == x, x * 3 / 3 * 3 == x * 3
{
    assert(x * 3 / 3 == x) by(nonlinear_arith);
    assert(x * 3 / 3 * 3 == x * 3) by(nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed requires syntax */
    let result = x * 3;
    proof {
        assert(x >= i32::MIN / 3 && x <= i32::MAX / 3);
        mul_3_div_3(x);
    }
    result
}
// </vc-code>

}
fn main() {}