// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diag(matrix: Vec<f32>, n: usize) -> (result: Vec<f32>)
    requires 
        matrix.len() == n * n,
        n > 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == matrix[i * n + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed index bounds checking with proper arithmetic reasoning */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == matrix@[j * n as int + j],
            n * n == matrix.len(),
        decreases n - i
    {
        // Since i < n and matrix.len() == n * n, we have:
        // i * n + i = i * (n + 1) < n * (n + 1) = n * n + n
        // Since n > 0 (from precondition), n * n + n > n * n
        // But we need i * n + i < n * n
        
        // Better reasoning: since i < n:
        // i * n + i = i * (n + 1) <= (n - 1) * (n + 1) = n^2 - 1 < n^2
        
        let index = i * n + i;
        
        // Prove index is valid
        proof {
            assert(i < n);
            assert(i * (n as int) + i == i * (n as int + 1));
            assert(i * (n as int + 1) < n * (n as int));
            assert(index < matrix.len());
        }
        
        result.push(matrix[index]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}