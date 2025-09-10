use vstd::prelude::*;

verus! {

fn log2(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures result.len() == x.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}