// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn find_last_nonzero_index(seq: Seq<f32>) -> (k: int)
    requires
        seq.len() > 0,
        seq[seq.len() - 1] == 0.0f32
    ensures
        0 <= k < seq.len(),
        forall|j: int| k < j < seq.len() ==> seq[j] == 0.0f32,
        k == 0 || seq[k] != 0.0f32
    decreases seq.len()
{
    /* helper modified by LLM (iteration 5): Changed to proof function to fix compilation error */
    let n = seq.len();
    if n == 1 {
        0
    } else if seq[n - 2] != 0.0f32 {
        n - 2
    } else {
        let subseq = seq.subrange(0, n - 1);
        assert(subseq.len() > 0) by { assert(n > 1); };
        assert(subseq[subseq.len() - 1] == seq[n - 2]) by { assert(n > 1); };
        assert(subseq[subseq.len() - 1] == 0.0f32) by { assert(seq[n - 1] == 0.0f32); };
        find_last_nonzero_index(subseq)
    }
}

spec fn has_trailing_zeros(seq: Seq<f32>) -> bool {
    seq.len() > 0 && seq[seq.len() - 1] == 0.0f32
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
{
    /* code modified by LLM (iteration 5): Fixed call to proof function by using proof block */
    let n = seq.len();
    if n == 0 || seq[n - 1] != 0.0f32 {
        seq
    } else {
        proof {
            let k = find_last_nonzero_index(seq@);
        }
        let mut result = Vec::with_capacity(n);
        let mut i = 0;
        while i < n 
            invariant
                0 <= i <= n,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == seq[j],
            decreases n - i
        {
            result.push(seq[i]);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}