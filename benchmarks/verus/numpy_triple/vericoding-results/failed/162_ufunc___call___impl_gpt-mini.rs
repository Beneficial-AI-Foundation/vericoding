// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): identity spec wrapper for op */
spec fn apply_op(op: spec_fn(f32, f32) -> f32, x: f32, y: f32) -> f32 { op(x, y) }
// </vc-helpers>

// <vc-spec>
fn ufunc_call(op: spec_fn(f32, f32) -> f32, a: &Vec<f32>, b: &Vec<f32>) -> (result: Vec<f32>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == op(a[i], b[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result from a spec sequence to avoid calling spec fn from exec mode */
    let n: int = a.len() as int;
    let s: Seq<f32> = spec { Seq::from_fn(n, |i: int| op(a@[i], b@[i])) };
    let result: Vec<f32> = Vec::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}