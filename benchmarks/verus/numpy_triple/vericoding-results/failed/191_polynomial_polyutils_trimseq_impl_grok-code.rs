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
                0 <= k < seq.len() as int &&

                (forall|j: int| k < j < seq.len() as int ==> seq[j] == 0.0f32) &&

                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() as int ==> result[i] == 0.0f32) &&

                (k > 0 ==> seq[k] != 0.0f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement trimseq by finding the last non-zero index and setting subsequent elements in result to 0, adding decreases clause */
    let len = seq.len();
    if len == 0 || seq[len - 1] != 0.0f32 {
        seq
    } else {
        let mut k: usize = len - 1;
        while k > 0 && seq[k - 1] == 0.0f32
            invariant
                k < len,
            decreases k
        {
            k -= 1;
        }
        // Now k is the last index where seq[k] != 0, or 0 if all are 0
        let mut result = seq;
        let mut i = k + 1;
        while i < len
            invariant
                k + 1 <= i <= len,
                forall |j: int| k < j < i as int ==> result[j] == 0.0f32,
                forall |j: int| 0 <= j <= k as int ==> result[j] == seq[j],
            decreases len - i
        {
            result[i] = 0.0f32;
            i += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}