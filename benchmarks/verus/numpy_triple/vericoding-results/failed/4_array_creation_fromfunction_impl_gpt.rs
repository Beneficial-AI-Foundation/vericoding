// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): construct a sequence from a spec function to avoid calling it in exec code */
spec fn seq_from_f(n: usize, f: spec_fn(usize) -> f32) -> Seq<f32> {
    Seq::new(n as int, |i: int| f(i as usize))
}
// </vc-helpers>

// <vc-spec>
fn fromfunction(n: usize, f: spec_fn(usize) -> f32) -> (result: Vec<f32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == f(i as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): build vector from a ghost sequence derived from the spec function */
    let ghost s: Seq<f32> = seq_from_f(n, f);
    let v: Vec<f32> = Vec::from_seq(s);
    v
}
// </vc-code>

}
fn main() {}