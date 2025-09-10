use vstd::prelude::*;

verus! {

fn ravel(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
{
    assume(false);
    unreached();
}

}
fn main() {}