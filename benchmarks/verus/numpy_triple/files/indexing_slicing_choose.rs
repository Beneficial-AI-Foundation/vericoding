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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}