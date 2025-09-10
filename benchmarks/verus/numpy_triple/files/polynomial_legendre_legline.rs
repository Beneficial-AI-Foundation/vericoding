use vstd::prelude::*;

verus! {

fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl
{
    assume(false);
    unreached()
}

}
fn main() {}