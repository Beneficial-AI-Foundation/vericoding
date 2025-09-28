// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified lemma for Seq::push properties without unnecessary casts */
proof fn lemma_seq_push_index_preserved<T>(s: Seq<T>, v: T)
    ensures
        s.push(v).len() == s.len() + 1,
        forall|j: int| 0 <= j < s.len() ==> s.push(v)[j] == s[j],
        s.push(v)[s.len()] == v,
{
    assert(s.push(v).len() == s.len() + 1);
    assert(forall|j: int| 0 <= j < s.len() ==> s.push(v)[j] == s[j]);
    assert(s.push(v)[s.len()] == v);
}
// </vc-helpers>

// <vc-spec>
fn ufunc_call(op: spec_fn(f32, f32) -> f32, a: &Vec<f32>, b: &Vec<f32>) -> (result: Vec<f32>)
    requires a@.len() == b@.len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == op(a@[i], b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct ghost sequence via op over views, then materialize Vec using from_seq */
    let ghost s: Seq<f32> = Seq::new(a@.len(), |i: int| op(a@[i], b@[i]));
    let result: Vec<f32> = Vec::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}