// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove mask@[j] is valid when j < i <= mask.len() */
proof fn mask_index_valid(mask: Seq<bool>, i: int, j: int)
    requires
        0 <= j < i,
        i <= mask.len(),
    ensures
        j < mask.len(),
{
    // Simple proof that j < i <= mask.len() implies j < mask.len()
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(mask: Seq<bool>) -> nat
    decreases mask.len()
{
    if mask.len() == 0 {
        0
    } else {
        (if mask[0] { 1nat } else { 0nat }) + count_true(mask.skip(1))
    }
}

fn place(arr: Vec<f32>, mask: Vec<bool>, vals: Vec<f32>) -> (result: Vec<f32>)
    requires 
        arr.len() == mask.len(),
        vals.len() > 0,
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> !mask[i] ==> result[i] == arr[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed index bounds and division by zero checks */
{
    let mut result = Vec::new();
    let mut val_idx: usize = 0;
    
    for i in 0..arr.len()
        invariant
            arr.len() == mask.len(),
            vals.len() > 0,
            result.len() == i,
            val_idx <= i,
            forall|j: int| 0 <= j < i && j < mask@.len() ==> !mask@[j] ==> result@[j] == arr@[j],
    {
        if mask[i] {
            if vals.len() > 0 {
                result.push(vals[val_idx % vals.len()]);
            }
            val_idx = val_idx + 1;
        } else {
            result.push(arr[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}