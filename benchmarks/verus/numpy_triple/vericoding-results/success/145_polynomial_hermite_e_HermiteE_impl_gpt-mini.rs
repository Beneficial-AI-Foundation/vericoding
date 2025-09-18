// <vc-preamble>
use vstd::prelude::*;

verus! {

struct HermiteEPoly {

    coef: Vec<f32>,

    domain_min: f32,

    domain_max: f32,

    window_min: f32,

    window_max: f32,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma that vector length is non-negative */
proof fn vec_len_nonneg(v: Vec<f32>) ensures v.len() >= 0 { }
// </vc-helpers>

// <vc-spec>
fn hermite_e(coef: Vec<f32>) -> (result: HermiteEPoly)
    ensures

        result.coef.len() == coef.len(),
        forall|i: int| 0 <= i < coef.len() ==> result.coef[i] == coef[i],

        result.domain_min == -1.0f32,
        result.domain_max == 1.0f32,

        result.window_min == -1.0f32,
        result.window_max == 1.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): move coef into result to preserve equality */
    let result = HermiteEPoly {
        coef: coef,
        domain_min: -1.0f32,
        domain_max: 1.0f32,
        window_min: -1.0f32,
        window_max: 1.0f32,
    };
    result
}
// </vc-code>

}
fn main() {}