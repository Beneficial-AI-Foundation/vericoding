// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn pi_quarter() -> (result: f64)
    ensures
        result == NPY_PI_4_EXACT,
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
    let result = pi_quarter();
    result
}
// </vc-code>


}
fn main() {}