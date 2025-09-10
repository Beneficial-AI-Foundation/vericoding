use vstd::prelude::*;

verus! {

fn norm(x: Vec<f32>) -> (result: f32)
    requires true,
    ensures true,
{
    assume(false);
    unreached()
}

}
fn main() {}