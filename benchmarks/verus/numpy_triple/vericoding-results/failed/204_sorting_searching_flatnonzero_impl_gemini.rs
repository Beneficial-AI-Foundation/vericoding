// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result@.len() ==> a[result@[i] as int] != 0.0,

        forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> result@[i] != result@[j],

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertion to relate old and new sequence after push, fixing invariant proof */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < result@.len() ==> result@[k] < i,
            forall|k: int| 0 <= k < result@.len() ==> a[result@[k] as int] != 0.0,
            forall|j: int| 0 <= j < i && a@[j] != 0.0 ==> 
                exists|k: int| 0 <= k < result@.len() && result@[k] == j as usize,
            forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() ==> 
                result@[k1] < result@[k2],
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            let old_result_seq = result@;
            result.push(i);
            assert(result@ == old_result_seq.push(i));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}