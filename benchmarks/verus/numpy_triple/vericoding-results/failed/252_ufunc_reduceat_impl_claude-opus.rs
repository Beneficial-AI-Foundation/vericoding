// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn slice_sum_equivalence(arr: Seq<i32>, start: int, end: int)
    requires
        0 <= start < end,
        end <= arr.len(),
    ensures
        start + 1 < end ==> slice_sum(arr, start, end) == slice_sum(arr, start, start + 1) + slice_sum(arr, start + 1, end),
        start + 1 == end ==> slice_sum(arr, start, end) == arr[start] as int,
    decreases end - start
{
    if start + 1 == end {
        assert(slice_sum(arr, start, end) == arr[start] as int);
    } else {
        assert(slice_sum(arr, start, end) == (arr[start] as int) + slice_sum(arr, start + 1, end));
        assert(slice_sum(arr, start, start + 1) == arr[start] as int);
        assert(slice_sum(arr, start, end) == slice_sum(arr, start, start + 1) + slice_sum(arr, start + 1, end));
    }
}

fn compute_slice_sum(arr: &Vec<i32>, start: usize, end: usize) -> (sum: i64)
    requires
        start <= end,
        end <= arr.len(),
    ensures
        sum == slice_sum(arr@, start as int, end as int),
    decreases end - start
{
    if start >= end {
        return 0;
    }
    
    let mut i = start;
    let mut total: i64 = 0;
    
    while i < end
        invariant
            start <= i <= end,
            end <= arr.len(),
            total == slice_sum(arr@, start as int, i as int),
        decreases end - i
    {
        proof {
            if i < end {
                slice_sum_equivalence(arr@, i as int, end as int);
            }
        }
        total = total + (arr[i] as i64);
        i = i + 1;
    }
    
    total
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
    /* code modified by LLM (iteration 4): Fixed precondition failures and type conversions */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let start_idx = indices[j] as int;
                if j < indices.len() - 1 {
                    let end_idx = indices[(j + 1) as int] as int;
                    if start_idx < end_idx {
                        #[trigger] (result[j] as int) == slice_sum(arr@, start_idx, end_idx)
                    } else {
                        start_idx < arr.len() &&
                        #[trigger] (result[j] as int) == arr[start_idx] as int
                    }
                } else {
                    #[trigger] (result[j] as int) == slice_sum(arr@, start_idx, arr.len() as int)
                }
            },
        decreases indices.len() - i
    {
        let start_idx = indices[i];
        
        let sum: i64 = if i < indices.len() - 1 {
            let end_idx = indices[i + 1];
            if start_idx < end_idx {
                compute_slice_sum(&arr, start_idx, end_idx)
            } else {
                arr[start_idx] as i64
            }
        } else {
            compute_slice_sum(&arr, start_idx, arr.len())
        };
        
        result.push(sum as i32);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}