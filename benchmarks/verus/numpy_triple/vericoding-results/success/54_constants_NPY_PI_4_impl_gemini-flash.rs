// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn npy_pi_4_helper() -> (result: f64)
    ensures result == NPY_PI_4_EXACT
{
    NPY_PI_4_EXACT
}
// </vc-helpers>

// <vc-spec>
const NPY_PI_4_EXACT: f64 = 0.785398163397448309615660845819875721;

fn npy_pi_4() -> (result: f64)
    ensures result == NPY_PI_4_EXACT
// </vc-spec>
// <vc-code>
{
    npy_pi_4_helper()
}
// </vc-code>


}
fn main() {}