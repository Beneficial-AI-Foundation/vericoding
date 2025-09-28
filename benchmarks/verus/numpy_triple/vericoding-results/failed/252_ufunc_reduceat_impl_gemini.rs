// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier::spinoff_prover]
proof fn slice_sum_append(arr: Seq<i32>, start: int, i: int)
    requires
        start <= i,
        i < arr.len(),
    ensures
        slice_sum(arr, start, i + 1) == slice_sum(arr, start, i) + arr[i] as int,
    decreases i - start
{
    if start < i {
        slice_sum_append(arr, start + 1, i);
    }
}

fn sum_slice_exec(arr: &Vec<i32>, start: usize, end: usize) -> (result: i32)
    requires
        start <= end,
        end <= arr.len(),
    ensures
        result as int == slice_sum(arr@, start as int, end as int),
{
    let mut sum: i32 = 0;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            end <= arr.len(),
            sum as int == slice_sum(arr@, start as int, i as int),
        decreases end - i
    {
        proof {
            slice_sum_append(arr@, start as int, i as int);
        }
        sum = sum + arr[i];
        i = i + 1;
    }
    sum
}
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
{
    /* code modified by LLM (iteration 2): fixed compilation errors by borrowing arr */
    let mut result_vec: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            arr.len() > 0,
            indices.len() > 0,
            forall|k: int| 0 <= k < indices.len() ==> (indices@[k] as int) < arr.len() as int,
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let start_idx = indices@[j] as int;
                if j < indices.len() - 1 {
                    let end_idx = indices@[j + 1] as int;
                    if start_idx < end_idx {
                        (#[trigger] result_vec@[j] as int) == slice_sum(arr@, start_idx, end_idx)
                    } else {
                        #[trigger] result_vec@[j] == arr@[start_idx]
                    }
                } else {
                    (#[trigger] result_vec@[j] as int) == slice_sum(arr@, start_idx, arr.len() as int)
                }
            },
        decreases indices.len() - i
    {
        let start_idx_usize = indices[i];
        if i < indices.len() - 1 {
            let end_idx_usize = indices[i + 1];
            if start_idx_usize < end_idx_usize {
                let val = sum_slice_exec(&arr, start_idx_usize, end_idx_usize);
                result_vec.push(val);
            } else {
                let val = arr[start_idx_usize];
                result_vec.push(val);
            }
        } else {
            let val = sum_slice_exec(&arr, start_idx_usize, arr.len());
            result_vec.push(val);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}