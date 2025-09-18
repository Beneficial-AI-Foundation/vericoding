// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide spec map2 from two sequences with a binary spec op */
spec fn map2(a: Seq<f32>, b: Seq<f32>, op: spec_fn(f32, f32) -> f32) -> Seq<f32>
    recommends a.len() == b.len()
{ Seq::new(a.len(), |i: int| op(a[i], b[i])) }

/* helper modified by LLM (iteration 5): lemma proving map2 preserves length */
proof fn map2_len(a: Seq<f32>, b: Seq<f32>, op: spec_fn(f32, f32) -> f32)
    requires a.len() == b.len()
    ensures map2(a, b, op).len() == a.len()
{ }

/* helper modified by LLM (iteration 5): lemma for pointwise relation of map2 */
proof fn map2_index(a: Seq<f32>, b: Seq<f32>, op: spec_fn(f32, f32) -> f32, i: int)
    requires a.len() == b.len(), 0 <= i < a.len()
    ensures map2(a, b, op)[i] == op(a[i], b[i])
{ }
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
    /* code modified by LLM (iteration 5): construct result from spec sequence using Vec::from to avoid calling spec op in exec context */
    let result: Vec<f32> = Vec::from(map2(a@, b@, op));
    result
}
// </vc-code>

}
fn main() {}