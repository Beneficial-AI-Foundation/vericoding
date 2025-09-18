// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires
        k > 0,
        arr.len() % k == 0,
    ensures
        result.len() == k,
        forall|i: int| #[trigger] result[i].len() == (arr.len() / k) ==> (0 <= i < k),
        forall|i: int, j: int| 
            0 <= i < k && 0 <= j < (arr.len() / k) as int ==> {
                let idx = i * (arr.len() / k) as int + j;
                0 <= idx < arr.len() as int && #[trigger] result[i][j] == arr[idx]
            },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed arithmetic overflow and added inner loop invariant */
{
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    for i in 0..k
        invariant
            result.len() == i,
            forall|idx: int| 0 <= idx < i as int ==> #[trigger] result[idx].len() == chunk_size,
            forall|idx: int, j: int|
                0 <= idx < i as int && 0 <= j < chunk_size as int ==> {
                    let arr_idx = idx * (chunk_size as int) + j;
                    0 <= arr_idx < arr.len() as int && #[trigger] result[idx][j] == arr@[arr_idx]
                }
    {
        let start = i * chunk_size;
        proof {
            assert(i < k);
            assert(chunk_size == arr.len() / k);
            assert(i * chunk_size < k * chunk_size);
            assert(k * chunk_size == arr.len());
            assert(start < arr.len());
        }
        let end = start + chunk_size;
        proof {
            assert(end == (i+1) * chunk_size);
            assert(i+1 <= k);
            assert((i+1) * chunk_size <= k * chunk_size);
            assert(k * chunk_size == arr.len());
            assert(end <= arr.len());
        }
        let mut chunk = Vec::new();
        for j_index in 0..chunk_size
            invariant
                chunk.len() == j_index,
                forall|j: int| 0<=j<j_index ==> chunk@[j] == arr@[start + j]
        {
            chunk.push(arr[start + j_index]);
        }
        result.push(chunk);
        proof {
            assert(forall|j: int| 0<=j<chunk_size as int ==> {
                let arr_idx = i * (chunk_size as int) + j;
                0 <= arr_idx < arr.len() as int && result[i][j] == arr@[arr_idx]
            });
        }
    }
    result
}
// </vc-code>

}
fn main() {}