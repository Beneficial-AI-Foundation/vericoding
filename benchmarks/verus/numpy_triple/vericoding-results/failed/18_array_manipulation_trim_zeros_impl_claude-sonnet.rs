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
/* helper modified by LLM (iteration 5): fixed loop body invariant violations by ensuring invariants are maintained */
fn find_first_nonzero(arr: &Vec<f32>) -> (start: usize)
    ensures
        start <= arr@.len(),
        start == arr@.len() || arr@[start as int] != 0.0f32,
        forall|i: int| 0 <= i < start ==> arr@[i] == 0.0f32
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr@.len(),
            forall|j: int| 0 <= j < i ==> arr@[j] == 0.0f32,
        decreases arr@.len() - i
    {
        if arr[i] != 0.0f32 {
            proof {
                assert(i < arr@.len());
                assert(arr@[i as int] != 0.0f32);
            }
            return i;
        }
        proof {
            assert(arr@[i as int] == 0.0f32);
        }
        i += 1;
    }
    proof {
        assert(i == arr@.len());
    }
    i
}

/* helper modified by LLM (iteration 5): fixed loop body invariant violations by ensuring invariants are maintained */
fn find_last_nonzero(arr: &Vec<f32>) -> (end: usize)
    ensures
        end <= arr@.len(),
        end == 0 || arr@[end as int - 1] != 0.0f32,
        forall|i: int| end <= i < arr@.len() ==> arr@[i] == 0.0f32
{
    let mut i = arr.len();
    while i > 0
        invariant
            0 <= i <= arr@.len(),
            forall|j: int| i <= j < arr@.len() ==> arr@[j] == 0.0f32,
        decreases i
    {
        if arr[i - 1] != 0.0f32 {
            proof {
                assert(i > 0);
                assert(arr@[i as int - 1] != 0.0f32);
            }
            return i;
        }
        proof {
            assert(arr@[i as int - 1] == 0.0f32);
        }
        i -= 1;
    }
    proof {
        assert(i == 0);
    }
    i
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
    /* code modified by LLM (iteration 5): fixed postcondition verification */
    let mut start = 0;
    let mut end = arr.len();
    
    match mode {
        TrimMode::Front => {
            start = find_first_nonzero(&arr);
        },
        TrimMode::Back => {
            end = find_last_nonzero(&arr);
        },
        TrimMode::Both => {
            start = find_first_nonzero(&arr);
            if start < arr.len() {
                end = find_last_nonzero(&arr);
            } else {
                end = start;
            }
        }
    }
    
    if start >= end {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut i = start;
    
    while i < end
        invariant
            start <= i <= end,
            end <= arr@.len(),
            result@.len() == i - start,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == arr@[start + j],
        decreases end - i
    {
        result.push(arr[i]);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}