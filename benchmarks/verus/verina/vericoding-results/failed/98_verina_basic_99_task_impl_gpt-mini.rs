// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma for i32 multiply/divide round-trip */
proof fn mul_div3_i32(x: i32) ensures (x * 3) / 3 == x && ((x * 3) / 3) * 3 == x * 3 {
    proof {
        assert((x * 3) / 3 == x);
        assert(((x * 3) / 3) * 3 == x * 3);
    }
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
    /* code modified by LLM (iteration 5): compute triple using i32 arithmetic and invoke helper proof */
    let result: i32 = x * 3;
    proof {
        mul_div3_i32(x);
    }
    result
}
// </vc-code>

}
fn main() {}