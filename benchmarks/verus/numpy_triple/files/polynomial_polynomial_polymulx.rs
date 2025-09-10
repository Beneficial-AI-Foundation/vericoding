use vstd::prelude::*;

verus! {

fn polymulx(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        forall|i: int| 0 <= i < c.len() ==> result[i + 1] == c[i],
{
    assume(false);
    unreached();
}

}
fn main() {}