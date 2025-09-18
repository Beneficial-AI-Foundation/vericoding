// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a decreases clause is not needed for helpers */
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
/* code modified by LLM (iteration 5): Added decreases clause to the while loop. */
{
    let mut result: Vec<f64> = Vec::new();
    result.resize(indices.len(), 0.0);
    let mut i: usize = 0;
    while i < indices.len()
        invariant
            indices.len() > 0,
            choices.len() > 0,
            forall|k: int| 0 <= k < indices.len() ==> indices[k] < choices.len(),
            forall|j: int| 0 <= j < choices.len() ==> choices[j].len() == indices.len(),
            0 <= i <= indices.len(),
            result.len() == indices.len(),
            forall|k: int| 0 <= k < i ==> result[k] == choices[indices[k] as int][k],
        decreases indices.len() - i
    {
        let choice_idx = indices[i];
        result.set(i, choices[choice_idx][i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}