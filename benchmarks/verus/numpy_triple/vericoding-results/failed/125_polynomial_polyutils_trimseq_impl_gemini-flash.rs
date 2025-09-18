// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Renamed parameters to avoid confusion */
spec fn check_zeros(s_seq: Seq<f32>, start: int, end: int) -> bool {
    forall|j: int| start <= j < end ==> s_seq[j] == 0.0f32
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
/* code modified by LLM (iteration 5): Changed invariant to reflect that found_non_zero is set when seq[k] is not zero. Also fixed invariant syntax. */
{
    let mut k: isize = 0;
    let mut found_non_zero: bool = false;

    if seq.len() == 0 {
        return seq;
    }

    k = (seq.len() as isize) - 1;
    while k >= 0
        decreases k
        invariant
            0 <= (k as int) + 1 <= seq.len() as int,
            (k as usize) < seq.len(),
            found_non_zero == (exists|i: int| (k as int) < i && i < (seq.len() as int) && seq@[i] != 0.0f32)
    {
        if seq[k as usize] != 0.0f32 {
            found_non_zero = true;
            break;
        }
        k = k - 1;
    }

    let mut result_vec = seq.clone();

    if found_non_zero {
        // k is the index of the last non-zero element from the right, or -1 if all are zero
        // We want to slice up to k (inclusive) but the original `len` will be kept.
        // Elements after k will be filled with 0s.
        proof {
            if k < (seq.len() as isize) - 1 {
                assert(check_zeros(seq@, (k as int) + 1, seq.len() as int));
            }
        }

        if k < (seq.len() as isize) - 1 {
            // Fill the rest with zeros
            let k_usize: usize = (k as usize);
            let mut i: usize = k_usize + 1;
            let len: usize = seq.len();
            while i < len
            decreases len - i
                invariant
                    k_usize < i <= len,
                    forall|j: int| (k as int) + 1 <= j && j < (i as int) ==> result_vec@[j] == 0.0f32,
                    result_vec.len() == seq.len(),
                    forall|j: int| 0 <= j && j <= (k as int) ==> result_vec@[j] == seq@[j],
            {
                result_vec[i as usize] = 0.0f32;
                i = i + 1;
            }
        }

    } else { // all elements are zero
        let mut i: usize = 0;
        let len: usize = seq.len();
        while i < len
            decreases len - i
            invariant
                i <= len,
                forall|j: int| 0 <= j && j < (i as int) ==> result_vec@[j] == 0.0f32,
                result_vec.len() == seq.len()
        {
            result_vec[i as usize] = 0.0f32;
            i = i + 1;
        }
    }

    result_vec
}
// </vc-code>

}
fn main() {}