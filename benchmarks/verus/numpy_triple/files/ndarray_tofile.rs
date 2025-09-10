use vstd::prelude::*;

verus! {

fn numpy_tofile(arr: Vec<f32>, filename: String) -> (result: ())
    requires true,
    ensures result == ()
{
    assume(false);
    unreached();
}

}
fn main() {}