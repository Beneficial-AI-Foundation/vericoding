// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed spec function with loops and simplified proof */
proof fn last_nonzero_properties(seq: &Vec<f32>, k: int)
    requires 0 <= k < seq.len(), seq@[k] != 0.0f32,
        forall|j: int| k < j < seq.len() ==> seq@[j] == 0.0f32
    ensures true
{
}
// </vc-helpers>

// <vc-spec>
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),

        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,

        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>

            exists|k: int| 
                0 <= k < seq.len() &&

                (forall|j: int| k < j < seq.len() ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch by casting i to int for sequence indexing */
{
    if seq.len() == 0 {
        return seq;
    }
    
    if seq[seq.len() - 1] != 0.0f32 {
        return seq;
    }
    
    let mut result = seq;
    let mut i = seq.len() - 1;
    
    while i > 0 && seq[i] == 0.0f32
        invariant
            i < seq.len(),
            forall|j: int| i < j < seq.len() ==> seq@[j] == 0.0f32
    {
        i = i - 1;
    }
    
    for j in (i + 1)..result.len()
        invariant
            result.len() == seq.len(),
            0 <= i < seq.len(),
            forall|idx: int| 0 <= idx <= i ==> result@[idx] == seq@[idx],
            forall|idx: int| i < idx < j ==> result@[idx] == 0.0f32,
            forall|idx: int| i < idx < seq.len() ==> seq@[idx] == 0.0f32,
            i == 0 || seq@[i as int] != 0.0f32
    {
        result.set(j, 0.0f32);
    }
    
    result
}
// </vc-code>

}
fn main() {}