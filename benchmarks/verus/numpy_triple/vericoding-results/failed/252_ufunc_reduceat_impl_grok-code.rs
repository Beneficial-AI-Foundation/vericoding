// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modifications needed, already correct */
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
/* code modified by LLM (iteration 5): Fixed Vec indexing to use int instead of usize */
{
    let mut result = Vec::new();
    let n = indices.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let start_idx_usize = indices@[j];
                let start_idx = start_idx_usize as int;
                if j < indices.len() as int - 1 {
                    let end_idx_usize = indices@[j + 1];
                    let end_idx = end_idx_usize as int;
                    if start_idx < end_idx {
                        #[trigger] result@[j] == slice_sum(arr@, start_idx, end_idx)
                    } else {
                        #[trigger] result@[j] == arr@[start_idx]
                    }
                } else {
                    #[trigger] result@[j] == slice_sum(arr@, start_idx, arr.len() as int)
                }
            },
        decreases n - i
    {
        if i + 1 < n {
            let start_idx = indices[i as int];
            let end_idx = indices[(i as int) + 1];
            if start_idx < end_idx {
                let sum = sum_range(&arr, start_idx, end_idx);
                result.push(sum);
            } else {
                result.push(arr[start_idx as int]);
            }
        } else {
            let start_idx = indices[i as int];
            let end_idx = arr.len();
            let sum = sum_range(&arr, start_idx, end_idx);
            result.push(sum);
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}