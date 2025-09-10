use vstd::prelude::*;

verus! {

spec fn shares_memory(a: Vec<f32>, b: Vec<f32>) -> bool
{

    true &&

    (a.len() == b.len() && a@ == b@) &&

    true &&

    true
}

fn shares_memory_fn(a: Vec<f32>, b: Vec<f32>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (a.len() == b.len() && a@ == b@ ==> result == true) &&

        true
{
    assume(false);
    unreached()
}

}
fn main() {}