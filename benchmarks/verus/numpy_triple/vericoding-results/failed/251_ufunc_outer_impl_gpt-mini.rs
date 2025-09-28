// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec and Seq lengths */
proof fn vec_seq_len<T>(v: &Vec<T>)
    ensures
        v@.len() == v.len(),
{
    assert(v@.len() == v.len());
}

// </vc-helpers>

// <vc-spec>
fn outer(op: spec_fn(f64, f64) -> f64, a: Vec<f64>, b: Vec<f64>) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
            result[i][j] == op(a[i], b[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result from nested sequence comprehensions */
    let s: Seq<Seq<f64>> = seq![|i: int| (seq![|j: int| op(a[i], b[j]) : 0 <= j < b.len()]) : 0 <= i < a.len()];
    Vec::from_seq(s)
}

// </vc-code>


}
fn main() {}