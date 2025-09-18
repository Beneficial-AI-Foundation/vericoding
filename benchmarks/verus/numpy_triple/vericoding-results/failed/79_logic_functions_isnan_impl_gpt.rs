// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma: (b == true) is equivalent to b */
proof fn lemma_true_eq_iff(b: bool) ensures (b == true) == b { }
/* helper modified by LLM (iteration 5): relate exec usize indexing with spec int indexing for self-inequality (handles NaN semantics) */
proof fn lemma_idx_neq_eq(x: &Vec<f64>, i: usize)
    requires i < x.len()
    ensures (x[i] != x[i]) == (x[i as int] != x[i as int])
{ }
// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute element-wise NaN check via self-inequality and maintain invariants without relying on branch conditions */
    let n = x.len();
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x.len() == n,
            r.len() == i,
            0 <= i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==> (r@[j] == true <==> x[j] != x[j])
        decreases n - i
    {
        let b = x[i] != x[i];
        r.push(b);
        proof {
            assert(r.len() == i + 1);
            assert(r@[i as int] == b);
            lemma_idx_neq_eq(&x, i);
            assert(b == (x[i as int] != x[i as int]));
            lemma_true_eq_iff(r@[i as int]);
            assert((r@[i as int] == true) == (x[i as int] != x[i as int]));
        }
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}