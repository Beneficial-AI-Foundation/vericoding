// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper lemma to prove slice_sum properties
proof fn lemma_slice_sum_single(arr: Seq<i32>, idx: int)
    requires
        0 <= idx < arr.len(),
    ensures
        slice_sum(arr, idx, idx + 1) == arr[idx] as int,
{
}

// Helper lemma for slice_sum bounds
proof fn lemma_slice_sum_bounds(arr: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= arr.len(),
    ensures
        slice_sum(arr, start, end) >= 0 || slice_sum(arr, start, end) < 0,
{
}

/* helper modified by LLM (iteration 5): fixed invariant and arithmetic properties */
// Helper function to compute sum of slice
fn compute_slice_sum(arr: &Vec<i32>, start: usize, end: usize) -> (sum: i32)
    requires
        start <= end,
        end <= arr.len(),
    ensures
        sum as int == slice_sum(arr@, start as int, end as int),
{
    let mut sum: i32 = 0;
    let mut i = start;
    
    while i < end
        invariant
            start <= i <= end,
            end <= arr.len(),
            sum as int == slice_sum(arr@, start as int, i as int),
        decreases (end - i)
    {
        proof {
            assert(i < end);
            assert(i < arr.len());
            // Help prove the invariant by showing slice_sum relationship
            assert(slice_sum(arr@, start as int, (i + 1) as int) == 
                   slice_sum(arr@, start as int, i as int) + arr@[i as int] as int);
        }
        sum = sum.wrapping_add(arr[i]);
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
    /* code modified by LLM (iteration 5): fixed bounds checks and precondition handling */
    let mut result: Vec<i32> = Vec::new();
    
    let mut i: usize = 0;
    while i < indices.len()
        invariant
            i <= indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let start_idx = indices[j] as int;
                if j < indices.len() - 1 {
                    let end_idx = indices[(j + 1) as int] as int;
                    if start_idx < end_idx {
                        #[trigger] (result[j] as int) == slice_sum(arr@, start_idx, end_idx)
                    } else {
                        #[trigger] result[j] == arr@[start_idx]
                    }
                } else {
                    #[trigger] (result[j] as int) == slice_sum(arr@, start_idx, arr.len() as int)
                }
            },
        decreases (indices.len() - i)
    {
        let start_idx = indices[i];
        
        // Use precondition to establish bounds
        proof {
            assert(0 <= i < indices.len());
            assert((indices[i] as int) < arr.len() as int);
            assert(start_idx < arr.len());
        }
        
        let sum = if i < indices.len() - 1 {
            let end_idx = indices[i + 1];
            if start_idx < end_idx {
                proof {
                    assert(0 <= (i + 1) < indices.len());
                    assert((indices[i + 1] as int) < arr.len() as int);
                    assert(end_idx <= arr.len());
                }
                compute_slice_sum(&arr, start_idx, end_idx)
            } else {
                arr[start_idx]
            }
        } else {
            compute_slice_sum(&arr, start_idx, arr.len())
        };
        
        result.push(sum);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}