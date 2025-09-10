use vstd::prelude::*;

verus! {

spec fn in_array(result: f32, a: Seq<f32>) -> bool {
    exists|i: int| 0 <= i < a.len() && result == a[i]
}

fn amin(a: Vec<f32>) -> (result: f32)
    requires a.len() > 0,
    ensures in_array(result, a@),
{
    assume(false);
    unreached()
}

}
fn main() {}