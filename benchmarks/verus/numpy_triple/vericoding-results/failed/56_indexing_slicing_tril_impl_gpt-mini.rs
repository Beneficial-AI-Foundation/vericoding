// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute row and column from flat index */
spec fn row(idx: usize, n: usize) -> usize { idx / n }
spec fn col(idx: usize, n: usize) -> usize { idx % n }
// </vc-helpers>

// <vc-spec>
fn tril(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        n > 0,
        matrix.len() == n * n,
    ensures
        result.len() == matrix.len(),
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == matrix[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement tril by iterating flattened indices with precise invariants */
    let len = matrix.len();
    let mut result: Vec<f32> = Vec::new();
    let mut idx: usize = 0;
    while idx < len
        invariant idx <= len;
        invariant result.len() == idx;
        invariant forall|k: usize| k < idx ==> result[k] == (if row(k, n) >= col(k, n) { matrix[k] } else { 0.0f32 });
        decreases len - idx;
    {
        let i = row(idx, n);
        let j = col(idx, n);
        if i < n && j < n && i >= j {
            result.push(matrix[idx]);
        } else {
            result.push(0.0f32);
        }
        idx = idx + 1;
    }
    proof {
        assert(result.len() == len);
        assert(forall|k: usize| k < len ==> result[k] == (if row(k, n) >= col(k, n) { matrix[k] } else { 0.0f32 }));
        assert(forall|i: usize, j: usize| (i < n && j < n && i >= j) ==> result[i * n + j] == matrix[i * n + j]);
        proof {
            fix(i: usize, j: usize);
            if i < n && j < n && i >= j {
                let k = i * n + j;
                assert(k < len);
                assert(row(k, n) == i);
                assert(col(k, n) == j);
                assert(result[k] == matrix[k]);
            }
        }
        assert(forall|i: usize, j: usize| (i < n && j < n && i < j) ==> result[i * n + j] == 0.0f32);
        proof {
            fix(i: usize, j: usize);
            if i < n && j < n && i < j {
                let k = i * n + j;
                assert(k < len);
                assert(row(k, n) == i);
                assert(col(k, n) == j);
                assert(result[k] == 0.0f32);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}