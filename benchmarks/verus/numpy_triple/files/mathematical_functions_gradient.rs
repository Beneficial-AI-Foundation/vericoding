use vstd::prelude::*;

verus! {

fn numpy_gradient(f: Vec<f64>) -> (grad: Vec<f64>)
    requires f.len() > 0,
    ensures
        grad.len() == f.len(),
        f.len() == 1 ==> grad[0] == 0.0,
{
    assume(false);
    unreached()
}

}
fn main() {}