// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that Vec and Seq indexing correspond */
proof fn vec_seq_index_correspondence(arr: &Vec<i32>, i: int)
    requires
        0 <= i,
        i < arr.len() as int,
    ensures
        arr@[i] == arr[i as usize],
{
    proof {
        assert(arr@[i] == arr[i as usize]);
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
/* code modified by LLM (iteration 5): compute per-index reductions using int/usize consistently and use lemma to relate Vec and Seq indexing */
{
    let mut result: Vec<i32> = Vec::new();
    let ilen: usize = indices.len();
    let mut i: usize = 0;
    while i < ilen
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==>
                if j < i as int - 1 {
                    if (indices[j] as int) < (indices[(j + 1) as int] as int) {
                        (result[j] as int) == slice_sum(arr@, indices[j] as int, indices[(j + 1) as int] as int)
                    } else {
                        result[j] == arr@[indices[j] as int]
                    }
                } else {
                    (result[j] as int) == slice_sum(arr@, indices[j] as int, arr.len() as int)
                },
        decreases
            ilen as int - i as int
    {
        let start_idx_usize = indices[i];
        let val: i32;
        if i + 1 < ilen {
            let end_idx_usize = indices[i + 1];
            if start_idx_usize < end_idx_usize {
                let mut s: i32 = 0;
                let mut j: usize = start_idx_usize;
                while j < end_idx_usize
                    invariant
                        start_idx_usize <= j,
                        j <= end_idx_usize,
                        (s as int) == slice_sum(arr@, start_idx_usize as int, j as int),
                    decreases
                        end_idx_usize as int - j as int
                {
                    s = s + arr[j];
                    j = j + 1;
                }
                val = s;
                proof {
                    assert((val as int) == slice_sum(arr@, start_idx_usize as int, end_idx_usize as int));
                }
            } else {
                val = arr[start_idx_usize];
                proof {
                    vec_seq_index_correspondence(&arr, start_idx_usize as int);
                    assert((val as int) == arr@[start_idx_usize as int]);
                }
            }
        } else {
            let mut s: i32 = 0;
            let mut j: usize = start_idx_usize;
            while j < arr.len()
                invariant
                    start_idx_usize <= j,
                    j <= arr.len(),
                    (s as int) == slice_sum(arr@, start_idx_usize as int, j as int),
                decreases
                    arr.len() as int - j as int
            {
                s = s + arr[j];
                j = j + 1;
            }
            val = s;
            proof {
                assert((val as int) == slice_sum(arr@, start_idx_usize as int, arr.len() as int));
            }
        }
        result.push(val);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}