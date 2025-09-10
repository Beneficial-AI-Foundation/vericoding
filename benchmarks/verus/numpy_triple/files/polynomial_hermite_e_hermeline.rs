use vstd::prelude::*;

verus! {

fn hermeline(off: f64, scl: f64) -> (coeffs: Vec<f64>)
    ensures
        coeffs.len() == 2,
        coeffs[0] == off,
        (scl == 0.0 ==> coeffs[1] == 0.0),
        (scl != 0.0 ==> coeffs[1] == scl)
{
    assume(false);
    unreached()
}

}
fn main() {}