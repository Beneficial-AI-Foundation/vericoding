use vstd::prelude::*;

verus! {

fn polydiv(c1: Vec<f32>, c2: Vec<f32>) -> (result: (Vec<f32>, Vec<f32>))
    requires 
        c1.len() > 0,
        c2.len() > 0,
        c2[c2.len() - 1] != 0.0f32,
    ensures ({
        let (quo, rem) = result;

        quo.len() == c1.len() &&
        rem.len() == c1.len() &&

        (forall|j: int| j >= (c2.len() - 1) && 0 <= j < rem.len() ==> rem[j] == 0.0f32)
    })
{
    assume(false);
    unreached()
}

}
fn main() {}