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
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == matrix[i * n + j] <==
            i < n && j < n && i >= j,
        forall|i: usize, j: usize| #[trigger] result[i * n + j] == 0.0f32 <==
            i < n && j < n && i < j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added explicit triggers and restructured loop invariants */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            n > 0,
            matrix.len() == n * n,
            0 <= i <= n,
            result.len() == i * n,
            forall|r_idx: usize, c_idx: usize|
                r_idx < i && c_idx < n && c_idx <= r_idx ==> 
                #[trigger] result@[r_idx * n + c_idx] == matrix@[r_idx * n + c_idx],
            forall|r_idx: usize, c_idx: usize|
                r_idx < i && c_idx < n && c_idx > r_idx ==> 
                #[trigger] result@[r_idx * n + c_idx] == 0.0f32,
        decreases n - i
    {
        let mut j = 0;
        while j < n
            invariant
                n > 0,
                matrix.len() == n * n,
                0 <= i < n,
                0 <= j <= n,
                result.len() == i * n + j,
                forall|r_idx: usize, c_idx: usize|
                    r_idx < i && c_idx < n && c_idx <= r_idx ==> 
                    #[trigger] result@[r_idx * n + c_idx] == matrix@[r_idx * n + c_idx],
                forall|r_idx: usize, c_idx: usize|
                    r_idx < i && c_idx < n && c_idx > r_idx ==> 
                    #[trigger] result@[r_idx * n + c_idx] == 0.0f32,
                forall|c_idx: usize|
                    c_idx < j && c_idx <= i ==> 
                    #[trigger] result@[i * n + c_idx] == matrix@[i * n + c_idx],
                forall|c_idx: usize|
                    c_idx < j && c_idx > i ==> 
                    #[trigger] result@[i * n + c_idx] == 0.0f32,
            decreases n - j
        {
            let index = i * n + j;
            if j <= i {
                result.push(matrix[index]);
            } else {
                result.push(0.0f32);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}