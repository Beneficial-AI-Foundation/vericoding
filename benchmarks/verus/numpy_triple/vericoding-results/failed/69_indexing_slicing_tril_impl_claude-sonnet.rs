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
{
    /* code modified by LLM (iteration 5): Added proper bounds checks and assertions to fix verification errors */
    let mut result = Vec::with_capacity(matrix.len());
    let mut k = 0;
    
    while k < matrix.len()
        invariant
            k <= matrix.len(),
            result.len() == k,
            n > 0,
            matrix.len() == n * n,
            forall|idx: usize| idx < k ==> {
                let i = idx / n;
                let j = idx % n;
                i < n && j < n && (if i >= j { result@[idx as int] == matrix@[idx as int] } else { result@[idx as int] == 0.0f32 })
            },
        decreases matrix.len() - k
    {
        assert(n > 0) by { /* from precondition */ };
        let i = k / n;
        let j = k % n;
        
        proof {
            assert(k < matrix.len());
            assert(matrix.len() == n * n);
            assert(k < n * n);
            assert(i == k / n && j == k % n);
            assert(i < n && j < n);
        }
        
        if i >= j {
            result.push(matrix[k]);
        } else {
            result.push(0.0f32);
        }
        k += 1;
    }
    
    proof {
        assert(result.len() == matrix.len());
        assert forall|i: usize, j: usize| i < n && j < n && i >= j implies {
            let idx = i * n + j;
            idx < matrix.len() && result@[idx as int] == matrix@[idx as int]
        } by {
            if i < n && j < n && i >= j {
                let idx = i * n + j;
                assert(idx < matrix.len());
                assert(idx / n == i && idx % n == j);
            }
        };
        assert forall|i: usize, j: usize| i < n && j < n && i < j implies {
            let idx = i * n + j;
            idx < matrix.len() && result@[idx as int] == 0.0f32
        } by {
            if i < n && j < n && i < j {
                let idx = i * n + j;
                assert(idx < matrix.len());
                assert(idx / n == i && idx % n == j);
            }
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}