// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Represents the trim mode for trim_zeros function */
#[derive(Eq, PartialEq)]
pub enum TrimMode {
    /* Trim zeros from the front of the array only (corresponds to 'f') */
    Front,
    /* Trim zeros from the back of the array only (corresponds to 'b') */
    Back,
    /* Trim zeros from both front and back of the array (corresponds to 'fb', default) */
    Both,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn trim_zeros(arr: Vec<f32>, mode: TrimMode) -> (result: Vec<f32>)
    ensures
        result@.len() <= arr@.len(),
        /* Result contains only elements from the original array */
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == arr@[j],
        /* Basic trimming properties based on mode */
        (mode == TrimMode::Front ==> 
            (result@.len() == 0 || result@[0] != 0.0f32)),
        (mode == TrimMode::Back ==> 
            (result@.len() == 0 || result@[result@.len() - 1] != 0.0f32)),
        (mode == TrimMode::Both ==> 
            (result@.len() == 0 || (result@[0] != 0.0f32 && result@[result@.len() - 1] != 0.0f32)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clauses to all loops */
    let mut start: usize = 0;
    let mut end: usize = arr.len();
    
    if matches!(mode, TrimMode::Front) || matches!(mode, TrimMode::Both) {
        while start < arr.len()
            invariant
                start <= arr.len(),
                forall|i: int| 0 <= i < start ==> arr@[i] == 0.0f32,
            decreases arr.len() - start
        {
            if arr[start] != 0.0f32 {
                break;
            }
            start = start + 1;
        }
    }
    
    if matches!(mode, TrimMode::Back) || matches!(mode, TrimMode::Both) {
        while end > start
            invariant
                start <= end,
                end <= arr.len(),
                forall|i: int| 0 <= i < start ==> arr@[i] == 0.0f32,
                forall|i: int| end <= i < arr@.len() ==> arr@[i] == 0.0f32,
            decreases end - start
        {
            if arr[end - 1] != 0.0f32 {
                break;
            }
            end = end - 1;
        }
    }
    
    let mut result = Vec::new();
    let mut i: usize = start;
    while i < end
        invariant
            start <= i,
            i <= end,
            end <= arr.len(),
            result@.len() == i - start,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == arr@[start + j],
            (matches!(mode, TrimMode::Front) || matches!(mode, TrimMode::Both)) ==> (start == arr@.len() || arr@[start as int] != 0.0f32),
            (matches!(mode, TrimMode::Back) || matches!(mode, TrimMode::Both)) ==> (end == start || arr@[(end - 1) as int] != 0.0f32),
        decreases end - i
    {
        result.push(arr[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}