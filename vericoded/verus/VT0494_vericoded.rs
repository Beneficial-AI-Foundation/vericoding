// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn legint(c: Vec<f64>, k: f64, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires scl != 0.0,
    ensures result@.len() == c@.len() + 1
// </vc-spec>
// <vc-code>
{
    let mut r: Vec<f64> = c.clone();
    r.push(0.0f64);
    r
}
// </vc-code>

}
fn main() {}