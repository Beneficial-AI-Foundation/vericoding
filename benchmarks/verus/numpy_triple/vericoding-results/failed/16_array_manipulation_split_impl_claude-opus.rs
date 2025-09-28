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
{
    /* code modified by LLM (iteration 3): Fixed arithmetic operations and indexing with proper bounds checking */
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < k
        invariant
            i <= k,
            result.len() == i,
            chunk_size == arr.len() / k,
            chunk_size > 0,
            i <= k,
            i * chunk_size <= arr.len(),
            forall|m: int| 0 <= m < i as int ==> result[m].len() == chunk_size,
            forall|m: int, n: int| 
                0 <= m < i as int && 0 <= n < chunk_size as int ==> {
                    let idx = m * chunk_size as int + n;
                    0 <= idx < arr.len() as int && result[m][n] == arr[idx as usize]
                },
        decreases k - i
    {
        let mut chunk: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        let start_idx: usize = i * chunk_size;
        
        proof {
            assert(i < k);
            assert(chunk_size == arr.len() / k);
            assert(arr.len() == k * chunk_size);
            assert(start_idx == i * chunk_size);
            assert(start_idx + chunk_size <= arr.len());
        }
        
        while j < chunk_size
            invariant
                j <= chunk_size,
                chunk.len() == j,
                start_idx == i * chunk_size,
                i < k,
                chunk_size > 0,
                start_idx + j <= arr.len(),
                start_idx + chunk_size <= arr.len(),
                forall|n: int| 0 <= n < j as int ==> chunk[n] == arr[start_idx + n as usize],
            decreases chunk_size - j
        {
            proof {
                assert(start_idx + j < arr.len());
            }
            chunk.push(arr[start_idx + j]);
            j = j + 1;
        }
        
        proof {
            assert(chunk.len() == chunk_size);
            assert(forall|n: int| 0 <= n < chunk_size as int ==> chunk[n] == arr[start_idx + n as usize]);
        }
        
        result.push(chunk);
        i = i + 1;
    }
    
    proof {
        assert(result.len() == k);
        assert(forall|m: int| 0 <= m < k ==> result[m].len() == chunk_size);
    }
    
    result
}
// </vc-code>

}
fn main() {}