use vstd::prelude::*;

verus! {

fn nancumprod(arr: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == arr.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}