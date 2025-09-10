use vstd::prelude::*;

verus! {

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
{
    assume(false);
    unreached()
}

}
fn main() {}