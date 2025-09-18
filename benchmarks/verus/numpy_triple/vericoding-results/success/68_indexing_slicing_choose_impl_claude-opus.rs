// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn choose(indices: Vec<usize>, choices: Vec<Vec<f64>>) -> (result: Vec<f64>)
    requires 
        indices.len() > 0,
        choices.len() > 0,
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < choices.len(),
        forall|j: int| 0 <= j < choices.len() ==> choices[j].len() == indices.len(),
    ensures 
        result.len() == indices.len(),
        forall|i: int| 0 <= i < indices.len() ==> result[i] == choices[indices[i] as int][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added assertions to help verify array bounds */
    let mut result = Vec::new();
    let n = indices.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == choices@[indices@[j] as int]@[j],
            indices.len() == n,
            forall|k: int| 0 <= k < indices.len() ==> indices@[k] < choices.len(),
            forall|k: int| 0 <= k < choices.len() ==> choices@[k].len() == indices.len()
        decreases n - i
    {
        assert(i < indices.len());
        let idx = indices[i];
        assert(idx < choices.len());
        assert(choices@[idx as int].len() == indices.len());
        assert(i < choices@[idx as int].len());
        let val = choices[idx][i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}