// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_non_zero(x: f64) -> bool {
    x != 0.0
}
/* helper modified by LLM (iteration 4): fixed ghost code usage */
// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices@.len() ==> 
            indices@[i] < a@.len() && a@[indices@[i] as int] != 0.0,

        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] != indices@[j],

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] < indices@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added asserts and auto triggers to fix invariants */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    let n = a.len();
    
    while i < n
        invariant
            i <= n,
            forall|j: int| 0 <= j < result@.len() ==> 
                result@[j] < a@.len() && a@[result@[j] as int] != 0.0,
            forall|j: int| #![auto] 0 <= j < i as int && a@[j] != 0.0 ==> 
                exists|k: int| 0 <= k < result@.len() && result@[k] == j as usize,
            forall|j1: int, j2: int| 0 <= j1 < j2 < result@.len() ==> 
                result@[j1] != result@[j2],
            forall|j1: int, j2: int| 0 <= j1 < j2 < result@.len() ==> 
                result@[j1] < result@[j2],
        decreases n - i
    {
        assert(i < a.len());
        if a[i] != 0.0 {
            result.push(i);
            assert(i < a.len() && a[i] != 0.0);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}