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
    /* code modified by LLM (iteration 3): added preconditions to loop invariants to resolve indexing errors */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            result.len() == i,
            forall|i_idx: int| 0 <= i_idx < indices.len() ==> indices[i_idx] < choices.len(),
            forall|j_idx: int| 0 <= j_idx < choices.len() ==> choices[j_idx].len() == indices.len(),
            forall|k: int| 0 <= k < i ==> result[k] == choices[indices[k] as int][k],
        decreases indices.len() - i,
    {
        let row_index = indices[i];
        let value = choices[row_index][i];
        result.push(value);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}