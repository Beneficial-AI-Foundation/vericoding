// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_two_vec(off: f64, scl: f64) -> (v: Vec<f64>)
    ensures
        v@.len() == 2,
        v@[0] == off,
        v@[1] == scl,
{
    let mut v: Vec<f64> = Vec::new();
    v.push(off);
    v.push(scl);
    v
}
// </vc-helpers>

// <vc-spec>
fn hermeline(off: f64, scl: f64) -> (coeffs: Vec<f64>)
    ensures
        coeffs@.len() == 2,
        coeffs@[0] == off,
        (scl == 0.0 ==> coeffs@[1] == 0.0),
        (scl != 0.0 ==> coeffs@[1] == scl)
// </vc-spec>
// <vc-code>
{
    make_two_vec(off, scl)
}
// </vc-code>

}
fn main() {}