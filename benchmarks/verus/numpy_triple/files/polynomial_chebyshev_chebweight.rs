use vstd::prelude::*;

verus! {

fn chebweight(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
{
    assume(false);
    unreached()
}

}
fn main() {}