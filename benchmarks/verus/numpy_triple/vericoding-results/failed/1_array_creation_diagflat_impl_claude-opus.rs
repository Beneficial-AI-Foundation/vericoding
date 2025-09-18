// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == v.len() * v.len(),
        forall|i: int| 0 <= i < v.len() ==> #[trigger] result[i * v.len() + i] == v[i],
        forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> #[trigger] result[i * v.len() + j] == 0.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow check and bounds verification */
    let n = v.len();
    if n == 0 {
        return Vec::new();
    }
    
    // Verify no overflow for n * n
    if n > usize::MAX / n {
        // Cannot create n*n sized vector
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < n * n
        invariant
            n > 0,
            n <= usize::MAX / n,
            i <= n * n,
            result.len() == i,
            forall|k: int| 0 <= k < i && k % (n as int) == k / (n as int) ==> #[trigger] result[k] == v[k / (n as int)],
            forall|k: int| 0 <= k < i && k % (n as int) != k / (n as int) ==> #[trigger] result[k] == 0.0f32
        decreases n * n - i
    {
        let row = i / n;
        let col = i % n;
        
        assert(row < n) by {
            assert(i < n * n);
            assert(i / n < n);
        };
        
        if row == col {
            assert(row < v.len());
            result.push(v[row]);
        } else {
            result.push(0.0f32);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}