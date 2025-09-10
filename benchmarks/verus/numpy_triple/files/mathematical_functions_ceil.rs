use vstd::prelude::*;

verus! {

fn numpy_ceil(x: Vec<f64>) -> (result: Vec<f64>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}