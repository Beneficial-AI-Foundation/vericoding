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
{
    /* code modified by LLM (iteration 5): fixed compilation error by removing invalid let statements inside assert forall bodies, replaced with direct assertions using calculated indices */
    let mut result = Vec::new();
    for k in 0..(n * n) {
        let i = k / n;
        let j = k % n;
        if i >= j {
            result.push(matrix[k]);
        } else {
            result.push(0.0f32);
        }
    }
    proof {
        assert(result.len() == matrix.len());
        assert forall |i: usize, j: usize| i < n && j < n && i >= j {
            let k = i * n + j;
            assert(k < n * n);
            assert(result@[k] == matrix@[k]);
        }
        assert forall |i: usize, j: usize| i < n && j < n && i < j {
            let k = i * n + j;
            assert(k < n * n);
            assert(result@[k] == 0.0f32);
        }
    }
    result
}
// </vc-code>

}
fn main() {}