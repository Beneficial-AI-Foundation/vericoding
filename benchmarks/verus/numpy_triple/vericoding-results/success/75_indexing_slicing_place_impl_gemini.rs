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
        forall|i: int| 0 <= i < arr.len() ==> !mask[i] ==> result[i] == arr[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added i <= arr.len() to loop invariant to prove result length */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            arr.len() == mask.len(),
            vals.len() > 0,
            i <= arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> !mask[k] ==> result[k] == arr[k],
        decreases arr.len() - i
    {
        if !mask[i] {
            result.push(arr[i]);
        } else {
            result.push(vals[0]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}