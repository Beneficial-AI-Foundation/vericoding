use vstd::prelude::*;

verus! {

fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}