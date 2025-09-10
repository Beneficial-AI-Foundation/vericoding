use vstd::prelude::*;

verus! {

fn numpy_flatiter(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i],
{
    assume(false);
    unreached()
}

}
fn main() {}