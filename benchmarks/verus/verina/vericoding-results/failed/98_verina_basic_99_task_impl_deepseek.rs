// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic quantifier and use manual arithmetic proof */
proof fn division_lemma(x: int, y: int)
    requires
        y > 0,
    ensures
        x / y * y <= x < (x / y + 1) * y,
{
    // Manual proof of division properties
    assert(x / y * y <= x) by (nonlinear_arith);
    assert(x < (x / y + 1) * y) by (nonlinear_arith);
}

proof fn triple_division_lemma(x: int)
    requires
        x >= -715827882 && x <= 715827882,
    ensures
        3 * x / 3 == x,
        3 * x % 3 == 0,
        3 * x / 3 * 3 == 3 * x,
{
    division_lemma(3 * x, 3);
    assert(3 * x / 3 == x) by (nonlinear_arith);
    assert(3 * x % 3 == 0) by (nonlinear_arith);
    assert(3 * x / 3 * 3 == 3 * x) by (nonlinear_arith);
}

fn triple_internal(x: i32) -> (result: i32)
    requires
        x >= -715827882 && x <= 715827882,
    ensures
        result == 3 * x,
{
    3 * x
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Maintain bounds verification and triple calculation */
{
    assert(-715827882 <= x && x <= 715827882) by {
        assert(-715827882 <= x && x <= 715827882) by (nonlinear_arith);
    };
    let result = triple_internal(x);
    proof {
        triple_division_lemma(x as int);
    }
    result
}
// </vc-code>

}
fn main() {}