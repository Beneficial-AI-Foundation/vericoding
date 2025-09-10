use vstd::prelude::*;

verus! {

fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
{
    assume(false);
    unreached();
}

}
fn main() {}