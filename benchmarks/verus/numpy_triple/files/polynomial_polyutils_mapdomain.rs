use vstd::prelude::*;

verus! {

fn mapdomain(x: Vec<f32>, old: Vec<f32>, new: Vec<f32>) -> (result: Vec<f32>)
    requires 
        old.len() == 2,
        new.len() == 2,
        old[1] != old[0],
    ensures
        result.len() == x.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}