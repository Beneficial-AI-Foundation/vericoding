use vstd::prelude::*;

verus! {

fn frexp(x: Vec<f32>) -> (result: (Vec<f32>, Vec<i32>))
    ensures
        result.0.len() == x.len(),
        result.1.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {

            x[i] == 0.0f32 ==> result.0[i] == 0.0f32 && result.1[i] == 0

        }
{
    assume(false);
    unreached()
}

}
fn main() {}