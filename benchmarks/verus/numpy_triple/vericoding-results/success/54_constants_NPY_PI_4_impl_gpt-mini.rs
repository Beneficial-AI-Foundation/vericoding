// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide a stable literal for pi/4 without referring to the spec constant */
fn pi_4_const() -> f64 {
    0.7853981633974483_f64
}
// </vc-helpers>

// <vc-spec>
const NPY_PI_4_EXACT: f64 = 0.785398163397448309615660845819875721;

fn npy_pi_4() -> (result: f64)
    ensures result == NPY_PI_4_EXACT
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return the pi/4 constant directly */
    let result: f64 = NPY_PI_4_EXACT;
    result
}
// </vc-code>


}
fn main() {}