// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 3): Add overflow check and proper arithmetic properties */
proof fn triple_properties(x: int)
    requires
        x >= -715827882 && x <= 715827882, // Safe range for i32 multiplication by 3
    ensures
        x * 3 == x + x + x,
        (x * 3) / 3 == x,
        (x * 3) / 3 * 3 == x * 3
{
    assert(x * 3 == x + x + x) by(nonlinear_arith);
    assert((x * 3) / 3 == x) by(nonlinear_arith);
    assert((x * 3) / 3 * 3 == x * 3) by(nonlinear_arith);
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
    /* code modified by LLM (iteration 3): Add overflow check and use proper proof structure */
    assert(-715827882 <= x && x <= 715827882) by(nonlinear_arith);
    let result = 3 * x;
    proof {
        triple_properties(x as int);
    }
    result
}
// </vc-code>

}
fn main() {}