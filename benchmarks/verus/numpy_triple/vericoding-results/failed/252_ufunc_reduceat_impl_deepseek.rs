// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_slice_sum_add(arr: Seq<i32>, start: int, mid: int, end: int)
    requires
        start <= mid <= end,
        end <= arr.len(),
    ensures
        slice_sum(arr, start, end) == slice_sum(arr, start, mid) + slice_sum(arr, mid, end),
    decreases (end - start)
{
    if start >= end {
        assert(slice_sum(arr, start, end) == 0) by {
            reveal(slice_sum);
        }
    } else if start + 1 == end {
        assert(slice_sum(arr, start, end) == arr[start] as int);
        assert(mid == end);
        assert(slice_sum(arr, mid, end) == 0);
    } else if start < mid {
        lemma_slice_sum_add(arr, start + 1, mid, end);
        assert(slice_sum(arr, start, end) == (arr[start] as int) + slice_sum(arr, start + 1, end));
        assert(slice_sum(arr, start, mid) == (arr[start] as int) + slice_sum(arr, start + 1, mid));
    } else {
        // mid == start
        assert(slice_sum(arr, start, start) == 0);
    }
}

proof fn lemma_slice_sum_prefix(arr: Seq<i32>, index: int, len: int)
    requires
        0 <= index <= len <= arr.len(),
    ensures
        slice_sum(arr, index, len) == slice_sum(arr.subrange(index, len), 0, len - index),
    decreases (len - index)
{
    if index >= len {
        assert(slice_sum(arr, index, len) == 0);
        assert(slice_sum(arr.subrange(index, len), 0, len - index) == 0);
    } else if index + 1 == len {
        assert(slice_sum(arr, index, len) == arr[index] as int);
        let sub = arr.subrange(index, len);
        assert(sub[0] == arr[index]);
        assert(slice_sum(sub, 0, 1) == sub[0] as int);
    } else {
        lemma_slice_sum_prefix(arr, index + 1, len);
        let sub = arr.subrange(index, len);
        assert(slice_sum(sub, 0, len - index) == (sub[0] as int) + slice_sum(sub, 1, len - index));
        assert(sub[0] == arr[index]);
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
{
    /* code modified by LLM (iteration 3): Fixed type casting in array indexing */
    let mut result: Vec<i32> = Vec::new();
    let arr_len = arr.len() as usize;
    let indices_len = indices.len();
    let mut i: usize = 0;
    
    while i < indices_len
        invariant
            0 <= i <= indices_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let start_idx = indices[j] as int;
                if j < indices_len - 1 {
                    let end_idx = indices[j + 1] as int;
                    if start_idx < end_idx {
                        result@[j] == slice_sum(arr@, start_idx, end_idx) as i32
                    } else {
                        result@[j] == arr[start_idx as usize]
                    }
                } else {
                    result@[j] == slice_sum(arr@, start_idx, arr_len as int) as i32
                }
            },
    {
        let start_idx = indices[i];
        let sum_val = if i < indices_len - 1 {
            let end_idx = indices[i + 1];
            if start_idx < end_idx {
                // Normal slice case
                let mut sum: i32 = 0;
                let mut j: usize = start_idx;
                
                while j < end_idx
                    invariant
                        start_idx <= j <= end_idx,
                        sum as int == slice_sum(arr@, start_idx as int, j as int),
                {
                    sum = sum + arr[j];
                    j = j + 1;
                }
                sum
            } else {
                // Single element case (non-increasing indices)
                arr[start_idx]
            }
        } else {
            // Last index case - reduce to end of array
            let mut sum: i32 = 0;
            let mut j: usize = start_idx;
            
            while j < arr_len
                invariant
                    start_idx <= j <= arr_len,
                    sum as int == slice_sum(arr@, start_idx as int, j as int),
            {
                sum = sum + arr[j];
                j = j + 1;
            }
            sum
        };
        
        result.push(sum_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}