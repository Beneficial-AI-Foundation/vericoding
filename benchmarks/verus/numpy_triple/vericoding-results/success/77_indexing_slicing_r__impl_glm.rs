// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn r_(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        forall|j: int| 0 <= j < b.len() ==> result[a.len() + j] == b[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added loop invariants to prove vector concatenation properties */
{
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k]
    {
        result.push(a[i]);
    }
    let a_len = a.len();
    for j in 0..b.len()
        invariant
            result.len() == a_len + j,
            forall|k: int| 0 <= k < a_len ==> result[k] == a[k],
            forall|k: int| 0 <= k < j ==> result[a_len + k] == b[k]
    {
        result.push(b[j]);
    }
    result
}
// </vc-code>

}
fn main() {}