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
        forall|i: int| 0 <= i < n as int ==> result@[i] == matrix@[i * n as int + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added trigger annotation to fix quantifier inference */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| #[trigger] (result@[j]) 0 <= j < i as int ==> result@[j] == matrix@[j * n as int + j],
            matrix.len() == n * n,
            n > 0,
        decreases n - i
    {
        assert(i < n);
        assert(i * n as int + i as int == i as int * n as int + i as int);
        assert((i as int * n as int + i as int) < (n as int * n as int));
        assert((i as int * n as int + i as int) < matrix.len() as int);
        let index = i * n + i;
        assert(index < matrix.len());
        let elem = matrix[index];
        result.push(elem);
        assert(result.len() == i + 1);
        assert(result@[i as int] == matrix@[i as int * n as int + i as int]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}