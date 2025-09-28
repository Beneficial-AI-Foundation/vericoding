// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed accumulator to int and added index bound invariant */
    #[verifier::spinoff_prover]
    fn compute_slice_sum(arr: &Vec<i32>, start: usize, end: usize) -> (sum: i32)
        requires 
            start <= end,
            end <= arr.len(),
        ensures 
            sum == slice_sum(arr@, start as int, end as int) as i32
    {
        if start == end {
            0
        } else {
            let mut s: int = 0;
            let mut i = start;
            while i < end
                invariant 
                    start <= i <= end,
                    i < arr.len(),
                    s == slice_sum(arr@, start as int, i as int),
                decreases end - i,
            {
                s += arr[i] as int;
                i += 1;
            }
            s as i32
        }
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
/* code modified by LLM (iteration 5): restructured loop invariants to avoid complex expressions */
    {
        let mut result = Vec::new();
        let n = indices.len();
        for i in 0..n
            invariant 
                result.len() == i,
                forall|j: int| 0 <= j < i && j < n-1 ==> 
                    (indices[j] < indices[j+1] ==> 
                        result[j] == slice_sum(arr@, indices[j] as int, indices[j+1] as int) as i32
                    ) &&
                    (indices[j] >= indices[j+1] ==> 
                        result[j] == arr[indices[j]]
                    ),
                forall|j: int| j == n-1 && j < i ==> 
                    result[j] == slice_sum(arr@, indices[j] as int, arr.len() as int) as i32
            decreases n - i,
        {
            if i < n - 1 {
                if indices[i] < indices[i+1] {
                    let s = compute_slice_sum(&arr, indices[i], indices[i+1]);
                    result.push(s);
                } else {
                    result.push(arr[indices[i]]);
                }
            } else {
                let s = compute_slice_sum(&arr, indices[i], arr.len());
                result.push(s);
            }
        }
        result
    }
// </vc-code>


}
fn main() {}