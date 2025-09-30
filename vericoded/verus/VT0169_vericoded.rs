// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn choose(indices: Vec<u8>, choices: Vec<Vec<f64>>) -> (result: Vec<f64>)
    requires 
        indices.len() > 0,
        choices.len() > 0,
        forall|i: int| 0 <= i < indices@.len() ==> (indices[i] as int) < (choices@.len() as int),
        forall|j: int| 0 <= j < choices@.len() ==> choices[j]@.len() == indices@.len(),
    ensures 
        result@.len() == indices@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> result[i] == choices[indices[i] as int][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added function preconditions to loop invariants to prove indexing safety */
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            result@.len() == (i as int),
            forall|k: int| 0 <= k < indices@.len() ==> (indices@[k] as int) < choices@.len(),
            forall|j: int| 0 <= j < choices@.len() ==> choices@[j]@.len() == indices@.len(),
            forall|k: int| 0 <= k < (i as int) ==> result@[k] == choices@[indices@[k] as int]@[k],
        decreases indices.len() - i
    {
        let index = indices[i];
        let value = choices[index as usize][i];
        result.push(value);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}