// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn polynomial(coef: Vec<f64>, domain: Vec<f64>, window: Vec<f64>) -> (result: Vec<f64>)
    requires 
        domain.len() == 2,
        window.len() == 2,
        domain[0] != domain[1],
        window[0] != window[1],
    ensures 
        result.len() == coef.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == coef[i],
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