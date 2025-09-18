// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add helper to check bounds and prevent overflow */
spec fn valid_capacity(len1: int, len2: int) -> bool {
    len1 > 0 && len2 > 0 && len1 + len2 - 1 > 0
}

spec fn is_all_zeros(v: Vec<f64>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v@[i] == 0.0
}
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
/* code modified by LLM (iteration 5): remove redundant proof block and asserts to fix compilation error */
{
    let capacity = c1.len() + c2.len() - 1;
    let mut result = Vec::with_capacity(capacity);
    for k in 0..capacity
        invariant
            0 <= k <= capacity,
            result.len() == k,
    {
        let mut sum = 0.0;
        for i in 0..(k+1)
            invariant
                0 <= i <= k + 1,
        {
            let j = k - i;
            if i < c1.len() && j < c2.len() {
                sum = sum + c1[i] * c2[j];
            }
        }
        result.push(sum);
    }
    result
}
// </vc-code>

}
fn main() {}