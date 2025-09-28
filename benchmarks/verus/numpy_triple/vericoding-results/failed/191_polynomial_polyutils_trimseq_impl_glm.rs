// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_last_nonzero_index(seq: &Vec<f32>) -> (k: int)
    requires
        seq.len() > 0,
    ensures
        0 <= k < seq.len() as int,
        (forall|j: int| k < j < seq.len() as int ==> seq[j] == 0.0f32),
        (k > 0 ==> seq[k] != 0.0f32)
{
    let mut i = seq.len() as int - 1;
    while i > 0 && seq[i] == 0.0f32
        invariant
            0 <= i < seq.len() as int,
            (forall|j: int| i < j < seq.len() as int ==> seq[j] == 0.0f32),
        decreases i
    {
        i = i - 1;
    }
    i
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
    if seq.len() == 0 {
        return Vec::new();
    }
    
    let last_element = seq[seq.len() - 1];
    if last_element != 0.0f32 {
        return seq;
    }
    
    let k = find_last_nonzero_index(&seq);
    
    let mut result = Vec::new();
    
    proof {
        reveal_with_fuel(find_last_nonzero_index, 2);
    }
    
    for i in 0..seq.len() {
        if i as int <= k {
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