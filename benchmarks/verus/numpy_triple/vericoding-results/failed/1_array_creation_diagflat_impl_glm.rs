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
/* code modified by LLM (iteration 5): fixed trigger inference issue by adding #[trigger] annotations to quantifier terms */
{
    let n = v.len();
    let mut result = Vec::new();
    result.resize(n * n, 0.0f32);

    for i in 0..n
        invariant
            result.len() == n * n,
            forall|idx: int| 0 <= idx < (n as int) * (n as int) ==> {
                let row = idx / (n as int);
                let col = idx % (n as int);
                if row < (i as int) && row == col {
                    #[trigger] result@[idx] == #[trigger] v@[row]
                } else {
                    #[trigger] result@[idx] == 0.0f32
                }
            }
    {
        let idx = i * n + i;
        result.set(idx, v[i]);
    }
    result
}
// </vc-code>

}
fn main() {}