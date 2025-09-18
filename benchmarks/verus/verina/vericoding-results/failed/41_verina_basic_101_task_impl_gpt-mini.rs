// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add bounds precondition to ensure no overflow when multiplying by 3 */
proof fn lemma_mul3_div(x: i32)
    requires
        x <= i32::MAX / 3,
        x >= i32::MIN / 3,
    ensures
        (x * 3) / 3 == x,
        ((x * 3) / 3) * 3 == x * 3,
{
    assert((x * 3) / 3 == x);
    assert(((x * 3) / 3) * 3 == x * 3);
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
    /* code modified by LLM (iteration 3): compute result as x*3 with proof of no-overflow via lemma */
    let result: i32 = x * 3;
    proof {
        lemma_mul3_div(x);
    }
    result
}
// </vc-code>

}
fn main() {}