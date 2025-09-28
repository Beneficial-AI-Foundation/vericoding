// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
        forall|i: int| 0 <= i < arr.len() ==> !mask@[i] ==> result@[i] == arr@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed arithmetic overflow by ensuring val_idx stays within bounds */
    let mut result = Vec::new();
    let mut val_idx: usize = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            arr.len() == mask.len(),
            vals.len() > 0,
            val_idx < vals.len(),
            forall|j: int| 0 <= j < i ==> !mask@[j] ==> result@[j] == arr@[j],
        decreases arr.len() - i
    {
        if mask[i] {
            result.push(vals[val_idx]);
            val_idx = if val_idx + 1 == vals.len() { 0 } else { val_idx + 1 };
        } else {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}