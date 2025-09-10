use vstd::prelude::*;

verus! {

fn tensorinv(a: Vec<Vec<f32>>, ind: usize) -> (result: Vec<Vec<f32>>)
    requires 
        a.len() > 0,
        ind > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == a.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}