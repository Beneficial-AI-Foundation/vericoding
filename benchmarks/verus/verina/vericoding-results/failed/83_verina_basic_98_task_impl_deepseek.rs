// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn triple_div_proof(x: int)  
    ensures triple_spec(x) / 3 == x {
    /* helper modified by LLM (iteration 5): fixed arithmetic proof */
    assert(triple_spec(x) == x * 3);
    assert(x * 3 / 3 == x) by (nonlinear_arith);
}
spec fn triple_spec(x: int) -> int {
    x * 3
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
    /* code modified by LLM (iteration 5): added overflow check and proof */
    proof {
        triple_div_proof(x as int);
    }
    assert(-2147483648 <= x && x <= 2147483647 / 3);
    let result = x * 3;
    assert(result / 3 == x);
    result
}
// </vc-code>

}
fn main() {}