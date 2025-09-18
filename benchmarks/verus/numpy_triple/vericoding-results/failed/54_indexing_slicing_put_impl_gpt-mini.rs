// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide min helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind.len() ==> ind[i] < a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < ind.len() ==> result[ind[i] as int] == v[i],
        forall|j: int| 0 <= j < result.len() ==> 
            (forall|i: int| 0 <= i < ind.len() ==> j != ind[i]) ==> result[j] == a[j],
        ind.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate indices with maintained invariants and proofs */
    let mut result = a.clone();
    let n = ind.len();
    let mut k: usize = 0;
    while k < n
        invariant k <= n && result.len() == a.len()
            && forall|i: int| 0 <= i < k as int ==> result[ind[i as usize]] == v[i as usize]
            && forall|i: int| 0 <= i < k as int ==> ind[i as usize] < result.len()
            && forall|i: int| 0 <= i < k as int ==> i as usize < v.len()
            && forall|j: int| 0 <= j < result.len() ==> (forall|i: int| 0 <= i < k as int ==> j as usize != ind[i as usize]) ==> result[j as usize] == a[j as usize]
        decreases n - k
    {
        let idx = ind[k];
        proof {
            // bounds for indexing
            assert(k < n);
            assert(k < ind.len());
            assert(k < v.len());
            // instantiate precondition that every ind[] is within a.len()
            assert(forall|i: int| 0 <= i < ind.len() ==> ind[i as usize] < a.len());
            assert(0 <= k as int && k as int < ind.len());
            assert(ind[k] < a.len());
            assert(ind[k] < result.len());
        }
        result.set(idx, v[k]);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}