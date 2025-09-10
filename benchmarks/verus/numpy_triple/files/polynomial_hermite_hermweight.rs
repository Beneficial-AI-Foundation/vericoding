use vstd::prelude::*;

verus! {

fn hermweight(x: Vec<f32>) -> (w: Vec<f32>)
    requires x.len() > 0,
    ensures
        w.len() == x.len(),
{
    assume(false);
    unreached()
}

}
fn main() {}