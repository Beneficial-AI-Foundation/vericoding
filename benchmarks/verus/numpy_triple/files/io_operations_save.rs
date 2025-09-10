use vstd::prelude::*;

verus! {

fn save(file: String, arr: Vec<f32>, allow_pickle: bool) -> (result: ())
    ensures result == (),
{
    assume(false);
    unreached();
}

}
fn main() {}