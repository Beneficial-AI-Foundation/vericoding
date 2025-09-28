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
/* helper modified by LLM (iteration 5): Removed `arr.is_empty()` check inside loop as it's redundant and caused compilation error; added `requires` clause to prevent empty `arr` from being passed in helper. */
fn find_first_nonzero_front(arr: &Vec<f32>) -> (idx: usize)
    requires
        arr@.len() > 0,
    ensures
        0 <= idx && idx <= arr@.len(),
        forall|i: int| 0 <= i < idx ==> arr@[i] == 0.0f32,
        idx < arr@.len() ==> arr@[idx as int] != 0.0f32,
{
    // This function will find the index of the first non-zero element from the front.
    // If all elements are zero, it returns arr.len().
    let mut idx = 0;
    while idx < arr.len()
        invariant 
            0 <= idx && idx <= arr@.len(),
            forall|i: int| 0 <= i < idx ==> arr@[i] == 0.0f32,
        decreases arr.len() - idx
    {
        if arr[idx] != 0.0f32 {
            break;
        }
        idx += 1;
    }
    idx
}

/* helper modified by LLM (iteration 5): Removed `arr.is_empty()` check inside loop as it's redundant and caused compilation error; added `requires` clause to prevent empty `arr` from being passed in helper. */
fn find_first_nonzero_back(arr: &Vec<f32>) -> (idx: isize)
    requires
        arr@.len() > 0,
    ensures
        -1 <= idx && (idx as int) < arr@.len(),
        forall|i: int| idx < i < arr@.len() ==> arr@[i] == 0.0f32,
        idx >= 0 ==> arr@[idx as int] != 0.0f32,
{
    // This function will find the index of the first non-zero element from the back.
    // If all elements are zero, it returns -1.
    let mut idx = arr.len() as isize - 1;
    while idx >= 0
        invariant 
            -1 <= idx && idx < arr@.len() as isize,
            forall|i: int| idx < i < arr@.len() ==> arr@[i] == 0.0f32,
        decreases idx + 1
    {
        if arr[idx as usize] != 0.0f32 {
            break;
        }
        idx -= 1;
    }
    idx
}
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
/* code modified by LLM (iteration 5): Added `arr.len() == 0` check before calling helper functions to avoid passing an empty `Vec` to helpers. */
{
    let arr_len = arr.len();
    if arr_len == 0 {
        return Vec::new();
    }

    let mut start_idx = 0;
    let mut end_idx = arr_len as isize - 1;

    if mode == TrimMode::Front || mode == TrimMode::Both {
        start_idx = find_first_nonzero_front(&arr);
    }

    if mode == TrimMode::Back || mode == TrimMode::Both {
        end_idx = find_first_nonzero_back(&arr);
    }

    if start_idx as isize > end_idx {
        Vec::new()
    } else {
        let mut result_vec = Vec::new();
        let mut i: usize = start_idx;
        while i <= end_idx as usize
            invariant
                start_idx <= i && i <= end_idx as usize + 1,
                result_vec@.len() == (i - start_idx) as int,
                forall|k: int| start_idx as int <= k && k < i as int ==> 
                    #[trigger] result_vec@[k - start_idx as int] == arr@[k],
            decreases (end_idx as usize) - i,
        {
            result_vec.push(arr[i]);
            i += 1;
        }
        result_vec
    }
}
// </vc-code>


}
fn main() {}