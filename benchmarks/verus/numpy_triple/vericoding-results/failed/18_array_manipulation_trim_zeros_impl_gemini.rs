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
    /* code modified by LLM (iteration 4): replaced unsupported `==` on enums with `match` to fix compilation error */
    let mut start: usize = 0;
    match mode {
        TrimMode::Front | TrimMode::Both => {
            let mut i: usize = 0;
            while i < arr.len() && arr[i] == 0.0f32
                invariant
                    0 <= i <= arr.len(),
                    forall|j: int| 0 <= j < (i as int) ==> arr@[j] == 0.0f32,
                decreases arr.len() - i
            {
                i = i + 1;
            }
            start = i;
        },
        _ => {},
    }

    let mut end: usize = arr.len();
    match mode {
        TrimMode::Back | TrimMode::Both => {
            let mut i: usize = arr.len();
            while i > start && arr[i - 1] == 0.0f32
                invariant
                    start <= i <= arr.len(),
                    forall|j: int| (i as int) <= j < arr@.len() ==> arr@[j] == 0.0f32,
                decreases i - start
            {
                i = i - 1;
            }
            end = i;
        },
        _ => {},
    }

    let mut result: Vec<f32> = Vec::new();
    let mut k: usize = start;
    while k < end
        invariant
            start <= k <= end,
            result@ == arr@.subrange(start as int, k as int),
        decreases end - k
    {
        result.push(arr[k]);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}