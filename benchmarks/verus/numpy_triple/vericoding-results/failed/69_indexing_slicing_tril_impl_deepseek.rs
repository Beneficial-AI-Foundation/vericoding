// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn tril_zero_lemma(matrix: Seq<f32>, n: nat, result: Seq<f32>)
    requires n > 0,
        matrix.len() == n * n,
        result.len() == n * n,
        forall|k: int| 0 <= k < n * n ==> (#[trigger] result[k] == matrix[k] && (k / n >= k % n) || #[trigger] result[k] == 0.0
    ensures
        forall|i: usize, j: usize| i < n && j < n && i >= j ==> #[trigger] result[i * n + j] == matrix[i * n + j],
        forall|i: usize, j: usize| i < n && j < n && i < j ==> #[trigger] result[i * n + j] == 0.0f32
{
    assert forall|i: usize, j: usize| i < n && j < n && i >= j implies #[trigger] result[i * n + j] == matrix[i * n + j] by {
        let idx: int = (i * n + j) as int;
        assert(0 <= idx < n * n);
        assert(idx / n == i as int);
        assert(idx % n == j as int);
        assert(i as int >= j as int);
    };
    assert forall|i: usize, j: usize| i < n && j < n && i < j implies #[trigger] result[i * n + j] == 0.0f32 by {
        let idx: int = (i * n + j) as int;
        assert(0 <= idx < n * n);
        assert(idx / n == i as int);
        assert(idx % n == j as int);
        assert(i as int < j as int);
    };
}
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
    /* code modified by LLM (iteration 5): fixed compilation error by removing unclosed parenthesis */
    let mut result = matrix.clone();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == matrix.len(),
            forall|k: int| 0 <= k < n * n ==> (k / n >= k % n ==> #[trigger] result[k as usize] == matrix[k as usize]) && (k / n < k % n ==> #[trigger] result[k as usize] == 0.0f32)
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                i < n,
                j <= n,
                result.len() == matrix.len(),
                forall|k: int| 0 <= k < n * n ==> 
                    ((k / n < i as int || (k / n == i as int && k % n < j as int)) && k % n < k / n ==> #[trigger] result[k as usize] == 0.0f32)
                    && (k / n < i as int && k % n >= k / n ==> #[trigger] result[k as usize] == matrix[k as usize])
            decreases n - j
        {
            if i < j {
                result.set(i * n + j, 0.0f32);
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        tril_zero_lemma(matrix@, n as nat, result@);
    }
    result
}
// </vc-code>

}
fn main() {}