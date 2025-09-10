use vstd::prelude::*;

verus! {

fn ascontiguousarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        a.len() > 0 ==> result.len() == a.len(),
        a.len() == 0 ==> result.len() == 1,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> exists|j: int| 0 <= j < result.len() && result[j] == a[i],
{
    assume(false);
    unreached();
}

}
fn main() {}