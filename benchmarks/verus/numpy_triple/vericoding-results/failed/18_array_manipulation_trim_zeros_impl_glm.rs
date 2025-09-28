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
/* helper modified by LLM (iteration 3): fixed type errors in postcondition and decreases clause */
fn find_first_nonzero(arr: &Vec<f32>) -> (idx: usize)
    ensures
        idx@ <= arr@.len(),
        forall|i: int| 0 <= i < idx@ ==> arr@[i] == 0.0f32,
        idx@ < arr@.len() ==> arr@[idx@ as int] != 0.0f32
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i@ <= arr@.len(),
            forall|j: int| 0 <= j < i@ ==> arr@[j] == 0.0f32
        decreases (arr@.len() - i)
    {
        if arr[i] != 0.0f32 {
            break;
        }
        i = i + 1;
    }
    i
}

/* helper modified by LLM (iteration 3): fixed type error in postcondition */
fn find_last_nonzero(arr: &Vec<f32>) -> (idx: Option<usize>)
    ensures
        idx.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] == 0.0f32,
        idx.is_some() ==> {
            let i = idx.unwrap();
            0 <= i@ < arr@.len() &&
            arr@[i@ as int] != 0.0f32 &&
            forall|j: int| i < j < arr@.len() ==> arr@[j] == 0.0f32
        }
{
    if arr.is_empty() {
        return None;
    }
    let mut i: usize = arr.len() - 1;
    while i > 0
        invariant
            0 <= i < arr.len(),
            forall|j: int| i < j < arr@.len() ==> arr@[j] == 0.0f32
        decreases i
    {
        if arr[i] != 0.0f32 {
            return Some(i);
        }
        i = i - 1;
    }
    if arr[0] != 0.0f32 {
        Some(0)
    } else {
        None
    }
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
{
    /* code modified by LLM (iteration 5): replaced slicing with explicit loops and simplified Both case */
    match mode {
        TrimMode::Front => {
            let start = find_first_nonzero(&arr);
            let mut result = Vec::new();
            let mut i = start;
            while i < arr.len() {
                result.push(arr[i]);
                i += 1;
            }
            result
        },
        TrimMode::Back => {
            let end = find_last_nonzero(&arr);
            match end {
                None => Vec::new(),
                Some(end) => {
                    let mut result = Vec::new();
                    let mut i = 0;
                    while i <= end {
                        result.push(arr[i]);
                        i += 1;
                    }
                    result
                }
            }
        },
        TrimMode::Both => {
            let start = find_first_nonzero(&arr);
            if start >= arr.len() {
                Vec::new()
            } else {
                let end = find_last_nonzero(&arr).unwrap();
                let mut result = Vec::new();
                let mut i = start;
                while i <= end {
                    result.push(arr[i]);
                    i += 1;
                }
                result
            }
        }
    }
}
// </vc-code>


}
fn main() {}