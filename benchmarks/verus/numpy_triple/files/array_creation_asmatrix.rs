use vstd::prelude::*;

verus! {

fn asmatrix(data: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
{
    assume(false);
    unreached()
}

}
fn main() {}