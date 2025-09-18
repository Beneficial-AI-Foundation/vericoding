// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed int_mul_int as it's not needed, raw multiplication is fine for usize */
// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == v.len() * v.len(),
        forall|i: int| 0 <= i < v.len() ==> #[trigger] result[i * v.len() + i] == v[i],
        forall|i: int, j: int| 0 <= i < v.len() && 0 <= j < v.len() && i != j ==> #[trigger] result[i * v.len() + j] == 0.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed all `int_mul_int` to direct multiplication and `as int` casts to `as usize` to resolve compilation errors. Corrected the `k < n * n` type handling. */
{
    let n: usize = v.len();
    let mut result: Vec<f32> = Vec::with_capacity(n * n);

    // Initialize result with zeros
    let mut k: usize = 0;
    while k < n * n
        invariant
            0 <= k && k <= n * n,
            result.len() == k,
            forall|idx: int| 0 <= idx && (idx as usize) < k ==> result@[idx] == 0.0f32
    {
        result.push(0.0f32);
        k = k + 1;
    }

    // Place elements of v on the diagonal
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            result.len() == n * n,
            forall|row: int, col: int| 0 <= row && (row as usize) < i && 0 <= col && (col as usize) < n ==> {
                if row == col {
                    result@[row * n + col] == v@[row]
                } else {
                    result@[row * n + col] == 0.0f32
                }
            },
            // For elements beyond 'i', they should still be 0.0
            forall|row: int, col: int| i <= (row as usize) && (row as usize) < n && 0 <= col && (col as usize) < n ==> {
                result@[row * n + col] == 0.0f32
            }
    {
        let idx = i * n + i;
        result.set(idx, v@[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}