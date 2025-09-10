use vstd::prelude::*;

verus! {

fn numpy_where(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        condition.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            (condition[i] ==> result[i] == x[i]) &&
            (!condition[i] ==> result[i] == y[i])
{
    assume(false);
    unreached()
}

}
fn main() {}