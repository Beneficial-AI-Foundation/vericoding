use vstd::prelude::*;

verus! {

fn cross(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    requires 
        a.len() == 3,
        b.len() == 3,
    ensures 
        result.len() == 3,
{
    assume(false);
    unreached()
}

}
fn main() {}