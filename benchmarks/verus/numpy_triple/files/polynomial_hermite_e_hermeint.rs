use vstd::prelude::*;

verus! {

fn hermeint(c: Vec<f64>, m: usize, k: Vec<f64>, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires 
        scl != 0.0,
        k.len() == m,
    ensures
        result.len() == c.len() + m,
        scl != 0.0,
        forall|step: int| 0 <= step < m ==> exists|contrib: f64| contrib == k[step],
{
    assume(false);
    unreached();
}

}
fn main() {}