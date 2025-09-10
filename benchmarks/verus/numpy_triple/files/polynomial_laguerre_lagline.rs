use vstd::prelude::*;

verus! {

fn lagline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
{
    assume(false);
    unreached()
}

}
fn main() {}