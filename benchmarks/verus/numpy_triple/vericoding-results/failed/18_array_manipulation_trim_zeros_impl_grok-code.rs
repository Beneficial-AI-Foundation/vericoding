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
    /* code modified by LLM (iteration 5): Fixed compilation by correcting Vec type, implemented correct trimming logic with loops for Vec construction and proper invariants */
    if mode == TrimMode::Front {
        let mut i: usize = 0;
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                forall|k: usize| k < i ==> arr@[k as int] == 0.0f32,
            decreases arr.len() - i
        {
            if arr[i] == 0.0f32 {
                i += 1;
            } else {
                break;
            }
        }
        // now i is the first non-zero index, or arr.len()
        if i >= arr.len() {
            return Vec::new();
        } else {
            let mut result = Vec::new();
            for j in i..arr.len() {
                result.push(arr[j]);
            }
            return result;
        }
    } else if mode == TrimMode::Back {
        let mut end: usize = arr.len();
        while end > 0 && arr[end - 1] == 0.0f32
            invariant
                0 <= end <= arr.len(),
                forall|k: usize| end <= k < arr.len() ==> arr@[k as int] == 0.0f32,
            decreases end
        {
            end -= 1;
        }
        // now end is the first index from start (0..end) is the prefix
        let mut result = Vec::new();
        for j in 0..end {
            result.push(arr[j]);
        }
        return result;
    } else { // Both
        let mut start: usize = 0;
        while start < arr.len()
            invariant
                0 <= start <= arr.len(),
                forall|k: usize| k < start ==> arr@[k as int] == 0.0f32,
            decreases arr.len() - start
        {
            if arr[start] == 0.0f32 {
                start += 1;
            } else {
                break;
            }
        }
        let mut end: usize = arr.len();
        while end > start && arr[end - 1] == 0.0f32
            invariant
                start <= end <= arr.len(),
                forall|k: usize| end <= k < arr.len() ==> arr@[k as int] == 0.0f32,
            decreases end - start
        {
            end -= 1;
        }
        if start >= end {
            return Vec::new();
        } else {
            let mut result = Vec::new();
            for j in start..end {
                result.push(arr[j]);
            }
            return result;
        }
    }
}
// </vc-code>


}
fn main() {}