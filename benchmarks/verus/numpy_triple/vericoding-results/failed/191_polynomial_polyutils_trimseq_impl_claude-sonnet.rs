// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper function to find the last non-zero index in a sequence
fn find_last_nonzero(seq: &Vec<f32>) -> (result: Option<usize>)
    requires
        seq.len() > 0,
    ensures
        match result {
            Some(idx) => {
                idx < seq.len() &&
                seq[idx as int] != 0.0f32 &&
                (forall|j: int| idx as int < j < seq.len() as int ==> seq[j] == 0.0f32)
            },
            None => {
                forall|i: int| 0 <= i < seq.len() as int ==> seq[i] == 0.0f32
            }
        }
{
    let mut i = seq.len();
    while i > 0
        invariant
            i <= seq.len(),
            forall|j: int| i as int <= j < seq.len() as int ==> seq[j] == 0.0f32,
        decreases i
    {
        i = i - 1;
        if seq[i as int] != 0.0f32 {
            return Some(i);
        }
    }
    None
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
{
    /* code modified by LLM (iteration 5): fixed syntax error by adding comma in forall expression */
    if seq.len() == 0 {
        return Vec::new();
    }
    
    let last_elem = seq[(seq.len() - 1) as int];
    if last_elem != 0.0f32 {
        return seq;
    }
    
    // Find the last non-zero element
    let last_nonzero_opt = find_last_nonzero(&seq);
    
    let mut result = Vec::with_capacity(seq.len());
    
    match last_nonzero_opt {
        Some(k) => {
            // Copy elements up to and including the last non-zero
            let mut i = 0;
            while i <= k
                invariant
                    i <= k + 1,
                    k < seq.len(),
                    result.len() == i,
                    forall|j: int| 0 <= j < i as int ==> result[j] == seq[j],
                decreases k - i
            {
                result.push(seq[i as int]);
                i = i + 1;
            }
            
            // Fill remaining positions with zeros
            while result.len() < seq.len()
                invariant
                    k + 1 <= result.len() <= seq.len(),
                    forall|j: int| 0 <= j <= k as int ==> result[j] == seq[j],
                    forall|j: int| k as int < j < result.len() as int ==> result[j] == 0.0f32,
                decreases seq.len() - result.len()
            {
                result.push(0.0f32);
            }
        },
        None => {
            // All elements are zero, create a vector of zeros
            while result.len() < seq.len()
                invariant
                    result.len() <= seq.len(),
                    forall|i: int| 0 <= i < result.len() as int ==> result[i] == 0.0f32,
                decreases seq.len() - result.len()
            {
                result.push(0.0f32);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}