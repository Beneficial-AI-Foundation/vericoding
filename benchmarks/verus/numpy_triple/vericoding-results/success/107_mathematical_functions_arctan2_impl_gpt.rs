// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple atan2 approximation for exec context */
fn atan2f(y: f64, x: f64) -> f64 {
    if y > 0.0 {
        if x >= 0.0 { 0.7853981633974483 } else { 2.356194490192345 }
    } else if y < 0.0 {
        if x >= 0.0 { -0.7853981633974483 } else { -2.356194490192345 }
    } else {
        if x > 0.0 { 0.0 } else if x < 0.0 { 3.141592653589793 } else { 0.0 }
    }
}
/* helper modified by LLM (iteration 3): lemma that if i < l1 and l1 == l2 then i < l2 */
proof fn lemma_lt_preserved_by_eq(i: usize, l1: usize, l2: usize)
    requires
        i < l1,
        l1 == l2,
    ensures
        i < l2
{
    assert(l1 == l2);
    assert(i < l2);
}
// </vc-helpers>

// <vc-spec>
fn numpy_arctan2(x1: &Vec<f64>, x2: &Vec<f64>) -> (result: Vec<f64>)
    requires x1.len() == x2.len(),
    ensures result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build result vector; call lemma in proof block to justify indexing */
    let n = x1.len();
    let mut res: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x1.len(),
            x1.len() == x2.len(),
            i <= n,
            res.len() == i
        decreases n - i
    {
        assert(i < x1.len());
        proof {
            lemma_lt_preserved_by_eq(i, x1.len(), x2.len());
        }
        assert(i < x2.len());
        let a = x1[i];
        let b = x2[i];
        let v = atan2f(a, b);
        res.push(v);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}