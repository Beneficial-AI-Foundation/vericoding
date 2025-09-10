use vstd::prelude::*;

verus! {

fn hermeder(c: Vec<f64>, m: usize, scl: f64) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        m > 0,
        scl != 0.0,
    ensures 
        result.len() == c.len() - 1,
{
    assume(false);
    unreached();
}

}
fn main() {}