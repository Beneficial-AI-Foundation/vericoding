// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to check all elements are zero */
spec fn is_all_zero(v: Vec<f64>) -> bool { forall|i: int| 0 <= i < v.len() ==> v[i] == 0.0 }
// </vc-helpers>

// <vc-spec>
fn hermemul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0) || 
        (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0) 
        ==> (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute Hermite polynomial multiplication (convolution); return zero vector early if one input is all zeros */
    let n = c1.len();
    let m = c2.len();
    let rl = n + m - 1;
    let mut result: Vec<f64> = Vec::new();

    let mut t: usize = 0;
    while t < rl
        invariant t <= rl
        invariant result.len() == t
        decreases rl - t
    {
        result.push(0.0);
        t += 1;
    }

    // If one of the inputs is all zeros, the convolution remains the zero vector
    if is_all_zero(c1) || is_all_zero(c2) {
        return result;
    }

    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant result.len() == rl
        decreases n - i
    {
        let mut j: usize = 0;
        while j < m
            invariant j <= m
            invariant result.len() == rl
            decreases m - j
        {
            let k = i + j;
            let val = result[k] + c1[i] * c2[j];
            result[k] = val;
            j += 1;
        }
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}