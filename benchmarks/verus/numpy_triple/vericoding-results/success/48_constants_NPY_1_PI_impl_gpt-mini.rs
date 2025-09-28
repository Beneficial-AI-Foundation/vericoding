// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proof that the fixed-point constant lies within bounds */
proof fn const_1_over_pi_bounds() {
    assert(0 < 318309886);
    assert(318309886 < 1000000000);
}

// </vc-helpers>

// <vc-spec>
fn npy_1_pi() -> (result: i32)
    ensures
        /* Mathematical constant representing 1/π as a fixed-point approximation */
        result > 0,
        /* Basic sanity check for positive value */
        result < 1000000000,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return fixed-point 1/pi and prove bounds */
    let result: i32 = 318309886;
    proof {
        const_1_over_pi_bounds();
    }
    result
}

// </vc-code>


}
fn main() {}