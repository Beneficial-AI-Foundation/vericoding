use vstd::prelude::*;

verus! {

fn asanyarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
{
    assume(false);
    unreached()
}

}
fn main() {}