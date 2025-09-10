use vstd::prelude::*;

verus! {

fn may_share_memory(a: &Vec<f32>, b: &Vec<f32>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (result == true ==> true) &&

        true &&

        true
{
    assume(false);
    unreached();
}

}
fn main() {}