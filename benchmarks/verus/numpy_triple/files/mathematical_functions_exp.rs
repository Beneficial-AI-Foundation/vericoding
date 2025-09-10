use vstd::prelude::*;

verus! {

fn numpy_exp(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}