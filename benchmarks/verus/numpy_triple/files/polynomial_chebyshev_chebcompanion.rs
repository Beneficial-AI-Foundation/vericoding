use vstd::prelude::*;

verus! {

fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c.len() >= 2,
    ensures
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
{
    assume(false);
    unreached();
}

}
fn main() {}