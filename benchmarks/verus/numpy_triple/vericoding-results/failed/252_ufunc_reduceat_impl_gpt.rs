// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma - extend slice_sum by one element (cat property for end) */
proof fn lemma_slice_sum_extend_right(arr: Seq<i32>, start: int, end: int)
    requires
        0 <= start,
        start <= end,
        end < arr.len(),
    ensures
        slice_sum(arr, start, end + 1) == slice_sum(arr, start, end) + (arr[end] as int),
    decreases end - start
{
    if start == end {
        assert(slice_sum(arr, start, start) == 0);
        assert(0 <= start && start < arr.len());
        assert(slice_sum(arr, start, start + 1) == arr[start] as int);
    } else {
        lemma_slice_sum_extend_right(arr, start + 1, end);
        assert(start < end + 1);
        assert(0 <= start && end + 1 <= arr.len());
        assert(slice_sum(arr, start, end + 1) == (arr[start] as int) + slice_sum(arr, start + 1, end + 1));
        assert(slice_sum(arr, start, end) == (arr[start] as int) + slice_sum(arr, start + 1, end));
        assert(slice_sum(arr, start + 1, end + 1) == slice_sum(arr, start + 1, end) + (arr[end] as int));
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
/* code modified by LLM (iteration 5): implement actual reduceat by iterating and summing slices; avoid exec int/nat usage */
{
    let n: usize = indices.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            n == indices.len(),
            forall|j: int| 0 <= j < i as int ==> {
                let start_idx = indices@[j] as int;
                if j < n as int - 1 {
                    let end_idx = indices@[(j + 1) as int] as int;
                    if start_idx < end_idx {
                        #[trigger] (res@[j] as int) == slice_sum(arr@, start_idx, end_idx)
                    } else {
                        #[trigger] res@[j] == arr@[start_idx]
                    }
                } else {
                    #[trigger] (res@[j] as int) == slice_sum(arr@, start_idx, arr.len() as int)
                }
            },
        decreases (n - i) as int
    {
        let start: usize = indices[i];
        let v: i32;
        if i + 1 < n {
            let end: usize = indices[i + 1];
            if start < end {
                let mut acc: i32 = 0;
                let mut k: usize = start;
                while k < end
                    invariant
                        start <= k,
                        k <= end,
                        (acc as int) == slice_sum(arr@, start as int, k as int),
                    decreases (end - k) as int
                {
                    proof { lemma_slice_sum_extend_right(arr@, start as int, k as int); }
                    acc = acc + arr[k];
                    k = k + 1;
                }
                v = acc;
                proof { assert((v as int) == slice_sum(arr@, start as int, end as int)); }
            } else {
                v = arr[start];
                proof { assert(v == arr@[start as int]); }
            }
        } else {
            let end: usize = arr.len();
            let mut acc: i32 = 0;
            let mut k: usize = start;
            while k < end
                invariant
                    start <= k,
                    k <= end,
                    (acc as int) == slice_sum(arr@, start as int, k as int),
                decreases (end - k) as int
            {
                proof { lemma_slice_sum_extend_right(arr@, start as int, k as int); }
                acc = acc + arr[k];
                k = k + 1;
            }
            v = acc;
            proof { assert((v as int) == slice_sum(arr@, start as int, end as int)); }
        }
        res.push(v);
        proof {
            let j: int = i as int;
            assert(indices@[j] == start);
            assert(res@[j] == v);
            if i + 1 < n {
                let end_us: usize = indices[i + 1];
                assert(indices@[(j + 1) as int] == end_us);
                if start < end_us {
                    assert((res@[j] as int) == slice_sum(arr@, start as int, end_us as int));
                } else {
                    assert(res@[j] == arr@[start as int]);
                }
            } else {
                assert((res@[j] as int) == slice_sum(arr@, start as int, arr.len() as int));
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}