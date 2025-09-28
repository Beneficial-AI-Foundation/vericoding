// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn tril(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        n > 0,
        matrix.len() == n * n,
    ensures
        result.len() == matrix.len(),
        forall|i: usize, j: usize| #[trigger] result@[i * n + j] == matrix@[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result@[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed trigger syntax in invariant, corrected indexing to use int, implemented matrix traversal logic to set lower triangular values. */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i * n,
            forall |k: int| #![trigger result@[k]] (0 <= k < result.len() && i >= 1) ==> {
                let row: int = k / (n as int);
                let col: int = k % (n as int);
                result@[k] == if row >= col { matrix@[k] } else { 0.0f32 }
            },
        decreases n - i,
    {
        let row_start: usize = i * n;
        let mut j: usize = 0;
        while j < n
            invariant
                result.len() == row_start + j,
            decreases n - j,
        {
            let idx: usize = row_start + j;
            let val: f32 = if i >= j { matrix[idx] } else { 0.0f32 };
            result.push(val);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}