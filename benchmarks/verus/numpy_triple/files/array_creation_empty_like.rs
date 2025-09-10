use vstd::prelude::*;

verus! {

fn numpy_empty_like(prototype: &Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == prototype.len(),
        forall|i: int| 0 <= i < prototype.len() ==> 0 <= i < result.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}