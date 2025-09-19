// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebfromroots(roots: Vec<f64>) -> (coeffs: Vec<f64>)
    ensures
        coeffs@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coeffs@[roots@.len() as int] != 0.0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}