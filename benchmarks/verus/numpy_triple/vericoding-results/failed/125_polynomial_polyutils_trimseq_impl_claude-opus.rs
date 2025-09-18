// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    let mut result = seq.clone();
    
    if seq.len() > 0 && seq[seq.len() - 1] == 0.0f32 {
        let mut k: usize = seq.len() - 1;
        
        while k > 0 {
            invariant
                k < seq.len(),
                forall|j: int| k < j < seq.len() ==> seq[j] == 0.0f32,
            decreases k
            {
                if seq[k] != 0.0f32 {
                    break;
                }
                k = k - 1;
            }
        
        if k == 0 && seq[0] == 0.0f32 {
            let mut i: usize = 0;
            while i < result.len() {
                invariant
                    i <= result.len(),
                    result.len() == seq.len(),
                    forall|j: int| 0 <= j < i ==> result[j] == 0.0f32,
                decreases result.len() - i
                {
                    result.set(i, 0.0f32);
                    i = i + 1;
                }
            proof {
                assert(k == 0);
                assert(forall|j: int| 0 < j < seq.len() ==> seq[j] == 0.0f32);
            }
        } else {
            let mut i: usize = k + 1;
            while i < result.len() {
                invariant
                    k < i <= result.len(),
                    result.len() == seq.len(),
                    forall|j: int| 0 <= j <= k ==> result[j] == seq[j],
                    forall|j: int| k < j < i ==> result[j] == 0.0f32,
                decreases result.len() - i
                {
                    result.set(i, 0.0f32);
                    i = i + 1;
                }
            proof {
                assert(k > 0 ==> seq[k] != 0.0f32);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}