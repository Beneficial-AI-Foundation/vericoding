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
    /* code modified by LLM (iteration 5): fixed while loop condition by removing parentheses to avoid parsing error */
    if seq.len() == 0 {
        return seq;
    }

    let mut k = seq.len() as int - 1;
    while k >= 0 && seq@[k] == 0.0f32
        invariant 0 <= k + 1 <= seq.len() as int
        invariant forall|j: int| k + 1 <= j < seq.len() as int ==> seq@[j] == 0.0f32
        decreases k
    {
        k -= 1;
    }

    if k < 0 {
        k = 0;
    }

    let mut result = seq;
    let mut i = k + 1;
    while i < seq.len() as int
        invariant forall|j: int| k+1 <= j < i ==> result@[j] == 0.0f32
        invariant forall|j: int| 0 <= j <= k ==> result@[j] == seq@[j]
        invariant forall|j: int| i <= j < seq.len() as int ==> result@[j] == seq@[j]
        decreases seq.len() as int - i
    {
        let i_usize = i as usize;
        result[i_usize] = 0.0f32;
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}