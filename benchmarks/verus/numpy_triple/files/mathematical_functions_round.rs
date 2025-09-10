use vstd::prelude::*;

verus! {

fn numpy_round(a: Vec<f64>, decimals: i32) -> (result: Vec<f64>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len()
{
    assume(false);
    unreached();
}

}
fn main() {}