// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn sinh_property(x: f64, result: f64) -> bool {

    true
}

fn sinh(x: Vec<f64>) -> (result: Vec<f64>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),

        forall|i: int| 0 <= i < x@.len() ==> sinh_property(x@[i], result@[i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}