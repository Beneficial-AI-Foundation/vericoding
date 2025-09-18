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
    /* code modified by LLM (iteration 5): Fixed type annotations and type mismatches by using int for indexing and providing explicit types. */
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    for i in 0..k
        invariant
            result.len() == i as int,
            forall|jj: int| 0 <= jj < i as int ==> result[jj].len() == chunk_size as int,
            forall|ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < chunk_size as int ==> {
                let idx = ii * (chunk_size as int) + jj;
                0 <= idx < arr.len() as int && result[ii][jj] == arr[idx]
            }
        {
        let mut chunk: Vec<f32> = Vec::new();
        for j in 0..chunk_size
            invariant
                chunk.len() == j as int,
                forall|jj: int| 0 <= jj < j as int ==> {
                    let idx_inner = (i as int) * (chunk_size as int) + jj;
                    chunk[jj] == arr[idx_inner]
                }
            {
            let idx_int = (i as int) * (chunk_size as int) + (j as int);
            proof { assert(idx_int < arr.len() as int); }
            chunk.push(arr[idx_int]);
        }
        result.push(chunk);
    }
    result
}
// </vc-code>

}
fn main() {}