use vstd::prelude::*;

verus! {

fn numpy_modf(x: Vec<f32>) -> (result: (Vec<f32>, Vec<f32>))
    ensures
        result.0.len() == x.len(),
        result.1.len() == x.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}