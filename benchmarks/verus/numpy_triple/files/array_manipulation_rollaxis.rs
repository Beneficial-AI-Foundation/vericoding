use vstd::prelude::*;

verus! {

fn numpy_rollaxis(a: Vec<f32>, axis: i32, start: i32) -> (result: Vec<f32>)
    ensures result == a
{
    assume(false);
    unreached()
}

}
fn main() {}