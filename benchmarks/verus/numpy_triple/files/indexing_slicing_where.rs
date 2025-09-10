use vstd::prelude::*;

verus! {

fn where_fn(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            result[i] == if condition[i] { x[i] } else { y[i] }
{
    assume(false);
    unreached();
}

}
fn main() {}