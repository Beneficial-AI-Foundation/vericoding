// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic assertions in lemma */
spec fn chunk_size(arr_len: usize, k: usize) -> usize
{
    arr_len / k
}

proof fn lemma_chunk_bounds(arr_len: usize, k: usize, i: usize, j: usize)
    requires
        k > 0,
        arr_len % k == 0,
        i < k,
        j < chunk_size(arr_len, k),
    ensures
        i * chunk_size(arr_len, k) + j < arr_len,
{
    let chunk_sz = chunk_size(arr_len, k);
    assert(arr_len / k == chunk_sz);
    assert(chunk_sz * k <= arr_len);
    assert(arr_len % k == 0) by {
        assert(chunk_sz * k + (arr_len % k) == arr_len);
    };
    assert(chunk_sz * k == arr_len);
    assert(i * chunk_sz + j < (i + 1) * chunk_sz) by {
        assert(j < chunk_sz);
    };
    assert((i + 1) * chunk_sz <= k * chunk_sz) by {
        assert(i + 1 <= k);
    };
    assert(k * chunk_sz == arr_len);
}

proof fn lemma_no_overflow(i: usize, chunk_sz: usize, j: usize, arr_len: usize, k: usize)
    requires
        k > 0,
        arr_len % k == 0,
        chunk_sz == arr_len / k,
        i < k,
        j < chunk_sz,
    ensures
        i * chunk_sz + j < usize::MAX,
{
    lemma_chunk_bounds(arr_len, k, i, j);
    assert(i * chunk_sz + j < arr_len);
}
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
/* code modified by LLM (iteration 5): added explicit trigger annotation for problematic forall */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let chunk_sz = arr.len() / k;
    
    for i in 0..k
        invariant
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx].len() == chunk_sz,
            forall|idx: int, j: int|
                0 <= idx < i && 0 <= j < chunk_sz as int ==> {
                    let arr_idx = idx * chunk_sz as int + j;
                    0 <= arr_idx < arr.len() as int && #[trigger] result[idx][j] == arr[arr_idx]
                },
    {
        let mut chunk: Vec<f32> = Vec::new();
        
        for j in 0..chunk_sz
            invariant
                chunk.len() == j,
                forall|jdx: int|
                    0 <= jdx < j ==> {
                        let arr_idx = i as int * chunk_sz as int + jdx;
                        0 <= arr_idx < arr.len() as int && #[trigger] chunk[jdx] == arr[arr_idx]
                    },
        {
            proof {
                lemma_chunk_bounds(arr.len(), k, i, j);
                lemma_no_overflow(i, chunk_sz, j, arr.len(), k);
            }
            let arr_idx = i * chunk_sz + j;
            chunk.push(arr[arr_idx]);
        }
        
        proof {
            assert(chunk.len() == chunk_sz);
            assert(forall|jdx: int| #[trigger] chunk[jdx] == arr[i as int * chunk_sz as int + jdx] ==> 0 <= jdx < chunk_sz as int ==> {
                let arr_idx = i as int * chunk_sz as int + jdx;
                0 <= arr_idx < arr.len() as int
            });
        }
        
        result.push(chunk);
    }
    
    proof {
        assert(result.len() == k);
        assert(forall|i: int| 0 <= i < k ==> result[i].len() == chunk_sz);
        assert(forall|i: int, j: int| 
            0 <= i < k && 0 <= j < chunk_sz as int ==> {
                let idx = i * chunk_sz as int + j;
                0 <= idx < arr.len() as int && result[i][j] == arr[idx]
            });
    }
    
    result
}
// </vc-code>

}
fn main() {}