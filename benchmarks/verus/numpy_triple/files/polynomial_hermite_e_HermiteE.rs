use vstd::prelude::*;

verus! {

struct HermiteEPoly {

    coef: Vec<f32>,

    domain_min: f32,

    domain_max: f32,

    window_min: f32,

    window_max: f32,
}

fn hermite_e(coef: Vec<f32>) -> (result: HermiteEPoly)
    ensures

        result.coef.len() == coef.len(),
        forall|i: int| 0 <= i < coef.len() ==> result.coef[i] == coef[i],

        result.domain_min == -1.0f32,
        result.domain_max == 1.0f32,

        result.window_min == -1.0f32,
        result.window_max == 1.0f32,
{
    assume(false);
    unreached();
}

}
fn main() {}