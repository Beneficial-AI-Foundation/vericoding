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
    /* code modified by LLM (iteration 5): Fixed all arithmetic and invariant issues */
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    proof {
        assert(arr.len() == k * chunk_size) by {
            assert(arr.len() % k == 0);
            assert(arr.len() / k * k == arr.len());
        }
    }
    
    while i < k
        invariant
            i <= k,
            result.len() == i,
            chunk_size == arr.len() / k,
            arr.len() == k * chunk_size,
            forall|m: int| 0 <= m < i as int ==> #[trigger] result[m].len() == chunk_size,
            forall|m: int, n: int| 
                0 <= m < i as int && 0 <= n < chunk_size as int ==> {
                    let idx = m * chunk_size as int + n;
                    0 <= idx < arr.len() as int && #[trigger] result[m][n] == arr[idx]
                },
        decreases k - i
    {
        let mut chunk: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        let start: usize = i * chunk_size;
        
        proof {
            assert(i < k);
            assert(start == i * chunk_size);
            assert(start + chunk_size <= arr.len()) by {
                assert(i < k);
                assert(start == i * chunk_size);
                assert(i * chunk_size + chunk_size == (i + 1) * chunk_size);
                assert((i + 1) * chunk_size <= k * chunk_size);
                assert(k * chunk_size == arr.len());
            }
        }
        
        while j < chunk_size
            invariant
                j <= chunk_size,
                chunk.len() == j,
                i < k,
                chunk_size == arr.len() / k,
                arr.len() == k * chunk_size,
                start == i * chunk_size,
                start + chunk_size <= arr.len(),
                forall|n: int| 0 <= n < j as int ==> {
                    let idx = start as int + n;
                    0 <= idx < arr.len() as int && #[trigger] chunk[n] == arr[idx]
                },
            decreases chunk_size - j
        {
            let idx = start + j;
            proof {
                assert(idx < arr.len()) by {
                    assert(j < chunk_size);
                    assert(start + j < start + chunk_size);
                    assert(start + chunk_size <= arr.len());
                }
            }
            chunk.push(arr[idx]);
            j = j + 1;
        }
        
        result.push(chunk);
        i = i + 1;
    }
    
    proof {
        assert(result.len() == k);
        assert forall|i: int| 0 <= i < k ==> #[trigger] result[i].len() == chunk_size by {
            assert forall|m: int| 0 <= m < k ==> result[m].len() == chunk_size;
        }
        assert forall|i: int| #[trigger] result[i].len() == (arr.len() / k) ==> (0 <= i < k) by {
            assert forall|i: int| 0 <= i < k ==> result[i].len() == chunk_size;
            assert(chunk_size == arr.len() / k);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}