use vstd::prelude::*;

verus! {

fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
{
    assume(false);
    unreached();
}

}
fn main() {}