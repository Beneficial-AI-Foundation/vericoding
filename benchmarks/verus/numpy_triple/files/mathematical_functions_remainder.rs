use vstd::prelude::*;

verus! {

fn remainder(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0.0,
    ensures
        result.len() == x1.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}