// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper functions are needed for this problem. */
// No helper functions are needed for this problem.
// </vc-helpers>

// <vc-spec>
spec fn slice_sum(arr: Seq<i32>, start: int, end: int) -> int
    decreases (end - start)
{
    if start >= end || start < 0 || end > arr.len() {
        0
    } else if start + 1 == end {
        arr[start] as int
    } else {
        (arr[start] as int) + slice_sum(arr, start + 1, end)
    }
}

fn reduceat_add(arr: Vec<i32>, indices: Vec<usize>) -> (result: Vec<i32>)
    requires 
        arr.len() > 0,
        indices.len() > 0,
        forall|i: int| 0 <= i < indices.len() ==> #[trigger] (indices[i] as int) < arr.len() as int,
    ensures
        result.len() == indices.len(),
        forall|i: int| 0 <= i < indices.len() ==> {
            let start_idx = indices[i] as int;
            if i < indices.len() - 1 {
                let end_idx = indices[(i + 1) as int] as int;
                if start_idx < end_idx {
                    /* Normal forward slice case */
                    #[trigger] (result[i] as int) == slice_sum(arr@, start_idx, end_idx)
                } else {
                    /* Single element case when indices are non-increasing */
                    #[trigger] result[i] == arr[start_idx]
                }
            } else {
                /* Last index case - reduce to end of array */
                #[trigger] (result[i] as int) == slice_sum(arr@, start_idx, arr.len() as int)
            }
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `usize` to `int` casts for array indexing in invariant clauses to match type requirements of `slice_sum` and array access. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < indices.len()
        invariant
            i <= indices.len(),
            result.len() == i,
            arr.len() > 0,
            indices.len() > 0,
            forall|k_idx: int| 0 <= k_idx < indices.len() ==> #[trigger] (indices[k_idx as usize] as int) < arr.len() as int,
            forall|k: int| 0 <= k < i ==> {
                let start_idx = indices[k as usize] as int;
                if k < (indices.len() as int) - 1 {
                    let end_idx = indices[((k + 1) as usize)] as int;
                    if start_idx < end_idx {
                        (result[k as usize] as int) == slice_sum(arr@, start_idx, end_idx)
                    } else {
                        result[k as usize] == arr[start_idx as usize]
                    }
                } else {
                    (result[k as usize] as int) == slice_sum(arr@, start_idx, arr.len() as int)
                }
            },
        decreases indices.len() - i
    {
        let start_idx_val = indices[i];
        let mut current_sum: i32 = 0;

        if i < indices.len() - 1 {
            let end_idx_val = indices[i + 1];
            if start_idx_val < end_idx_val {
                // Calculate sum for a normal forward slice
                let mut j = start_idx_val;
                while j < end_idx_val
                    invariant
                        start_idx_val <= j,
                        j <= end_idx_val,
                        current_sum as int == slice_sum(arr@, start_idx_val as int, j as int),
                        arr.len() > 0,
                        indices.len() > 0,
                        forall|k_idx: int| 0 <= k_idx < indices.len() ==> #[trigger] (indices[k_idx as usize] as int) < arr.len() as int,
                    decreases end_idx_val - j
                {
                    current_sum = current_sum + arr[j];
                    j = j + 1;
                }
            } else {
                // Single element case when indices are non-increasing
                current_sum = arr[start_idx_val];
            }
        } else {
            // Last index case - reduce to end of array
            let mut j = start_idx_val;
            while j < arr.len()
                invariant
                    start_idx_val <= j,
                    j <= arr.len(),
                    current_sum as int == slice_sum(arr@, start_idx_val as int, j as int),
                    arr.len() > 0,
                    indices.len() > 0,
                    forall|k_idx: int| 0 <= k_idx < indices.len() ==> #[trigger] (indices[k_idx as usize] as int) < arr.len() as int,
                decreases arr.len() - j
            {
                current_sum = current_sum + arr[j];
                j = j + 1;
            }
        }
        result.push(current_sum);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}