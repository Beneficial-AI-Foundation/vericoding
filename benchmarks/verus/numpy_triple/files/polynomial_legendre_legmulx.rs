use vstd::prelude::*;

verus! {

fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
        forall|i: int| 0 <= i < result.len() ==> exists|coeff: f32| result[i] == coeff,
{
    assume(false);
    unreached();
}

}
fn main() {}