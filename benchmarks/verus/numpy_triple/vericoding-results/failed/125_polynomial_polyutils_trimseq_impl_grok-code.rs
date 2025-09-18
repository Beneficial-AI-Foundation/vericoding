// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatch by casting result to int for sequence indexing */
fn find_last_non_zero_index(seq: &Vec<f32>) -> (result: usize)
    requires true
    ensures
        seq@.len() == 0 ==> result == 0,

        seq@.len() != 0 ==> {
            let k = result as int;
            0 <= k < seq@.len() &&
            (forall |j: int| k < j < seq@.len() ==> seq@[j] == 0.0f32) &&
            (result > 0 ==> seq@[(result as int)] != 0.0f32)
        }
{
    if seq.len() == 0 {
        return 0;
    }
    let mut k = seq.len();
    while k > 0
        decreases k
    {
        k -= 1;
        if seq[k] != 0.0f32 {
            return k;
        }
    }
    return 0;
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
/* code modified by LLM (iteration 5): Ensured proper handling of k as int for spec compliance */
{
    let k_usize = find_last_non_zero_index(&seq);
    let k = k_usize as int;
    assert(0 <= k < seq@.len() || seq.len() == 0);
    let mut result = Vec::<f32>::new();
    result.reserve(seq.len());
    for i in 0..seq.len() {
        if i <= k_usize {
            result.push(seq[i]);
        } else {
            result.push(0.0f32);
        }
    }
    result
}
// </vc-code>

}
fn main() {}