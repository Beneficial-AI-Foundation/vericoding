use vstd::prelude::*;

verus! {

fn legint(c: Vec<f64>, k: f64, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires scl != 0.0,
    ensures result.len() == c.len() + 1
{
    assume(false);
    unreached()
}

}
fn main() {}