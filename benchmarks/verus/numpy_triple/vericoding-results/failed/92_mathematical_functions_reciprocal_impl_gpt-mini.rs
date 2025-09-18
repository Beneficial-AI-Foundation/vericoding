// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): reciprocal of a non-zero float */
fn reciprocal_elem(x: f32) -> f32
    requires x != 0.0_f32
{
    1.0_f32 / x
}
// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i] != 0.0_f32,
    ensures
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute reciprocals using usize indices without casting to int */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    let len: usize = x.len();
    while i < len
        invariant i <= len && result.len() == i
        decreases len - i
    {
        proof {
            let idx: int = i as int;
            assert(0 <= idx);
            assert(idx < (len as int));
            assert(x@[idx] != 0.0_f32);
        }
        let xi: f32 = x[i];
        let ri: f32 = reciprocal_elem(xi);
        result.push(ri);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}