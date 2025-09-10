use vstd::prelude::*;

verus! {

fn rot90(m: Vec<Vec<f32>>, k: i32) -> (result: Vec<Vec<f32>>)
    requires
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() == m.len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m.len()
{
    assume(false);
    unreached();
}

}
fn main() {}