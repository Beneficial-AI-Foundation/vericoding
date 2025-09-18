// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): utility selector for branching between two f32 values */
spec fn pick(cond: bool, a: f32, b: f32) -> f32 { if cond { a } else { b } }
/* helper modified by LLM (iteration 3): lemma that pushing to a Seq preserves previous indices */
proof fn seq_index_of_push_preserved_f32(s: Seq<f32>, v: f32, j: int)
    requires 0 <= j < s.len()
    ensures s.push(v)[j] == s[j]
{ }
// </vc-helpers>

// <vc-spec>
fn numpy_where(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == x.len(),
        condition.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> 
            (condition[i] ==> result[i] == x[i]) &&
            (!condition[i] ==> result[i] == y[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed int-in-exec issue; loop builds result with invariants over vector views */
    let n = condition.len();
    let mut r: Vec<f32> = Vec::new();
    while r.len() < n
        invariant
            r.len() <= n,
            n == condition.len(),
            n == x.len(),
            n == y.len(),
            forall|j: int| 0 <= j < r.len() as int ==>
                (condition[j] ==> r@[j] == x[j]) &&
                (!condition[j] ==> r@[j] == y[j])
        decreases (n as int) - (r.len() as int)
    {
        let idx = r.len();
        let v = if condition[idx] { x[idx] } else { y[idx] };
        r.push(v);
    }
    assert(r.len() == n);
    r
}
// </vc-code>

}
fn main() {}