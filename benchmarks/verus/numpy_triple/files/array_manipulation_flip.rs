use vstd::prelude::*;

verus! {

fn numpy_flip(m: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> result[i] == m[m.len() - 1 - i],
{
    assume(false);
    unreached();
}

}
fn main() {}