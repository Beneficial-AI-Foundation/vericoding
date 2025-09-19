// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagval(x: Vec<f64>, c: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c@.len() > 0,
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}