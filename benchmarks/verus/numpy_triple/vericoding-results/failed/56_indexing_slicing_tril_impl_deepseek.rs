// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches in helper functions by casting nat to int */
spec fn is_lower_triangular(matrix: Seq<f32>, n: nat) -> bool {
    forall|i: nat, j: nat| i < n && j < n && i < j ==> matrix[i as int * n as int + j as int] == 0.0f32
}

proof fn tril_preserves_original_values(matrix: Seq<f32>, result: Seq<f32>, n: nat)
    requires
        n > 0,
        matrix.len() == n * n,
    ensures
        forall|i: nat, j: nat| i < n && j < n && i >= j ==> result[i as int * n as int + j as int] == matrix[i as int * n as int + j as int]
{
}

proof fn tril_sets_upper_to_zero(matrix: Seq<f32>, result: Seq<f32>, n: nat)
    requires
        n > 0,
        matrix.len() == n * n,
    ensures
        forall|i: nat, j: nat| i < n && j < n && i < j ==> result[i as int * n as int + j as int] == 0.0f32
{
}

/* helper modified by LLM (iteration 5): Removed vec_with_len helper to avoid conflicts */
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
/* code modified by LLM (iteration 5): Fixed type mismatches by casting usize to int in indexing operations */
{
    let mut result = Vec::with_capacity(matrix.len());
    let mut k: usize = 0;
    while k < matrix.len() {
        result.push(0.0f32);
        k = k + 1;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == matrix.len(),
            forall|row: usize, col: usize| row < i && col < n && row >= col ==> #[trigger] result[row as int * n as int + col as int] == matrix[row as int * n as int + col as int],
            forall|row: usize, col: usize| row < i && col < n && row < col ==> #[trigger] result[row as int * n as int + col as int] == 0.0f32,
            forall|k: usize| k >= i * n && k < matrix.len() ==> result[k] == 0.0f32
    {
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                forall|col: usize| col < j && i >= col ==> #[trigger] result[i as int * n as int + col as int] == matrix[i as int * n as int + col as int],
                forall|col: usize| col < j && i < col ==> #[trigger] result[i as int * n as int + col as int] == 0.0f32
        {
            if i >= j {
                result[i as int * n as int + j as int] = matrix[i as int * n as int + j as int];
            } else {
                result[i as int * n as int + j as int] = 0.0f32;
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