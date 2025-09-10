use vstd::prelude::*;

verus! {

fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
{
    assume(false);
    unreached();
}

}
fn main() {}