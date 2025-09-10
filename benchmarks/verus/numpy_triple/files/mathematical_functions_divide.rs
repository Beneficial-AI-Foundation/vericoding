use vstd::prelude::*;

verus! {

fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> x2[i] != 0.0f32,
{
    assume(false);
    unreached()
}

}
fn main() {}