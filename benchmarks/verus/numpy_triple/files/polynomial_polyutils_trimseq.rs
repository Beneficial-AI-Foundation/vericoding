/* Remove small Poly series coefficients.

Remove trailing zeros from a sequence of polynomial coefficients.
Returns the sequence with trailing zeros removed. If the sequence would be empty 
after trimming, returns the first element. Empty sequences are handled.

Specification: trimseq removes trailing zeros while preserving at least one element.
For non-empty sequences, if the last element is non-zero, return the sequence unchanged.
If the last element is zero, trim trailing zeros but always keep at least one element. */

use vstd::prelude::*;

verus! {
fn trimseq(seq: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == seq.len(),
        /* If empty or last element is non-zero, return unchanged */
        (seq.len() == 0 || (seq.len() > 0 && seq[seq.len() - 1] != 0.0f32)) ==> result@ == seq@,
        /* If last element is zero, trim properly */
        (seq.len() > 0 && seq[seq.len() - 1] == 0.0f32) ==>
            /* There exists a position k where trimming occurs */
            exists|k: int| 
                0 <= k < seq.len() &&
                /* All elements after k in original sequence are zero */
                (forall|j: int| k < j < seq.len() ==> seq[j] == 0.0f32) &&
                /* Result preserves elements up to k, zeros after */
                (forall|i: int| 0 <= i <= k ==> result[i] == seq[i]) &&
                (forall|i: int| k < i < result.len() ==> result[i] == 0.0f32) &&
                /* Element at k is non-zero unless k = 0 (all zeros case) */
                (k > 0 ==> seq[k] != 0.0f32)
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}