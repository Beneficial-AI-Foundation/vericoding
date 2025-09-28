// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute last non-zero index k using int indices */
proof fn find_k(seq: &Vec<f32>) -> (k: int)
    requires
        seq.len() > 0,
        seq[seq.len() - 1] == 0.0f32,
    ensures
        0 <= k,
        k < seq.len() as int,
        forall|j: int| k < j && j < seq.len() as int ==> seq@[j] == 0.0f32,
        k > 0 ==> seq@[k] != 0.0f32,
{
    let n: int = seq.len() as int;
    let mut i: int = 0;
    let mut k: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            0 <= k && k < n,
            k <= i,
            forall|j: int| k < j && j < i ==> seq@[j] == 0.0f32,
        decreases n - i
    {
        if seq@[i] != 0.0f32 {
            k = i;
        }
        i = i + 1;
    }
    k
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
    /* code modified by LLM (iteration 5): construct result preserving prefix up to k and zeros after */
    let n = seq.len();
    let mut result: Vec<f32> = Vec::new();
    if n == 0 {
        return result;
    }
    if seq[n - 1] != 0.0f32 {
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                result.len() == i,
            decreases n - i
        {
            result.push(seq[i]);
            i = i + 1;
        }
        return result;
    } else {
        let k_int = find_k(&seq);
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                result.len() == i,
            decreases n - i
        {
            if (i as int) <= k_int {
                result.push(seq[i]);
            } else {
                result.push(0.0f32);
            }
            i = i + 1;
        }
        return result;
    }
}
// </vc-code>

}
fn main() {}