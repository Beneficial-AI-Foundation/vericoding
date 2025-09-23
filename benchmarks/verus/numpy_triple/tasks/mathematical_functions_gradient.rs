// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_gradient(f: Vec<f64>) -> (grad: Vec<f64>)
    requires f.len() > 0,
    ensures
        grad.len() == f.len(),
        f.len() == 1 ==> grad[0] == 0.0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}