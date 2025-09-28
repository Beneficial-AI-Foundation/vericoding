// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence indexing syntax */
fn trimseq_helper(seq: &Vec<f32>, k: usize) -> (result: Vec<f32>)
    requires
        k < seq.len(),
        forall|j: int| k < j < seq.len() as int ==> seq@[j] == 0.0f32,
        k == 0 || seq@[k] != 0.0f32,
    ensures
        result.len() == seq.len(),
        forall|i: int| 0 <= i <= k as int ==> result@[i] == seq@[i],
        forall|i: int| k as int < i < result.len() as int ==> result@[i] == 0.0f32,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < seq.len()
        invariant
            i <= seq.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (if j <= k as int { seq@[j] } else { 0.0f32 }),
        decreases seq.len() - i,
    {
        if i <= k {
            result.push(seq[i]);
        } else {
            result.push(0.0f32);
        }
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),

        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,

        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>

            exists|k: int| 
                0 <= k < seq.len() as int &&

                (forall|j: int| k < j < seq.len() as int ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() as int ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed tuple indexing and added proper termination */
{
    if seq.is_empty() {
        seq
    } else {
        let seq_len = seq.len();
        let last_elem = seq[seq_len - 1];
        
        if last_elem != 0.0f32 {
            seq
        } else {
            let mut k: usize = 0;
            let mut i: usize = 0;
            
            while i < seq_len
                invariant
                    i <= seq_len,
                    k <= i,
                    forall|j: int| k <= j < i as int ==> seq@[j] == 0.0f32,
                    k == 0 || (k > 0 && seq@[k - 1] != 0.0f32),
                decreases seq_len - i,
            {
                if seq[i] != 0.0f32 {
                    k = i + 1;
                }
                i = i + 1;
            }
            
            trimseq_helper(&seq, k)
        }
    }
}
// </vc-code>

}
fn main() {}