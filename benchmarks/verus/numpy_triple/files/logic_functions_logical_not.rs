use vstd::prelude::*;

verus! {

fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
{
    assume(false);
    unreached()
}

}
fn main() {}