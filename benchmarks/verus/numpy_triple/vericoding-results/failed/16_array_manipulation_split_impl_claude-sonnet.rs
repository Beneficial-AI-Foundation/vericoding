// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type consistency for int operations */
fn bounds_check_mult_add(i: usize, chunk_size: usize, j: usize, arr_len: usize) -> (result: bool)
    requires
        chunk_size > 0,
    ensures
        result == (i <= usize::MAX / chunk_size && i * chunk_size <= usize::MAX - j && i * chunk_size + j < arr_len),
{
    i <= usize::MAX / chunk_size && i * chunk_size <= usize::MAX - j && i * chunk_size + j < arr_len
}

fn valid_index_calculation(i: int, chunk_size: int, j: int, arr_len: int) -> (result: bool)
    requires
        chunk_size > 0,
    ensures
        result == (i * chunk_size + j >= 0int && i * chunk_size + j < arr_len),
{
    i * chunk_size + j >= 0int && i * chunk_size + j < arr_len
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
{
    /* code modified by LLM (iteration 5): fixed integer literal type consistency */
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < k
        invariant
            i <= k,
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx].len() == chunk_size,
            forall|idx: int, j: int| 
                0 <= idx < i && 0 <= j < chunk_size as int ==> {
                    let arr_idx = idx * chunk_size as int + j;
                    0 <= arr_idx < arr.len() as int && #[trigger] result[idx][j] == arr[arr_idx]
                },
        decreases k - i,
    {
        let mut chunk: Vec<f32> = Vec::new();
        let mut j = 0;
        
        while j < chunk_size
            invariant
                j <= chunk_size,
                chunk.len() == j,
                i < k,
                i * chunk_size + j <= arr.len(),
                forall|idx: int| 0 <= idx < j ==> {
                    let arr_idx = i * chunk_size + idx;
                    0 <= arr_idx < arr.len() && #[trigger] chunk[idx] == arr[arr_idx]
                },
            decreases chunk_size - j,
        {
            proof {
                assert(i < k);
                assert(j < chunk_size);
                assert(i * chunk_size + j < arr.len());
            }
            let arr_idx = i * chunk_size + j;
            chunk.push(arr[arr_idx]);
            j += 1;
        }
        
        proof {
            assert(chunk.len() == chunk_size);
            assert(forall|j_val: int| 0 <= j_val < chunk_size as int ==> {
                let arr_idx = i * chunk_size as int + j_val;
                0 <= arr_idx < arr.len() as int && chunk[j_val] == arr[arr_idx]
            });
        }
        
        result.push(chunk);
        i += 1;
    }
    
    proof {
        assert(result.len() == k);
        assert(forall|i: int| 0 <= i < k ==> result[i].len() == chunk_size);
        assert(forall|i: int| 0 <= i < k ==> result[i].len() == arr.len() / k);
    }
    
    result
}
// </vc-code>

}
fn main() {}