// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagint(c: Vec<f64>, m: usize, k: Vec<f64>, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires 
        k.len() == m,
        scl != 0.0,
    ensures 
        result.len() == c.len() + m
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