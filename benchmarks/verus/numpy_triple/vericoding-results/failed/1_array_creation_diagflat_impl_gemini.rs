// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to prove termination */
fn new_zero_vec(len: usize) -> (result: Vec<f32>)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i < len ==> result@[i] == 0.0f32,
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 0.0f32,
        decreases len - i,
    {
        result.push(0.0f32);
        i = i + 1;
    }
    result
}
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
    /* code modified by LLM (iteration 5): added decreases clause to prove termination */
    let n = v.len();
    let mut result = new_zero_vec(n * n);

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n * n,
            // Off-diagonal elements in processed rows (k < i) are zero.
            forall|k: int, j: int|
                0 <= k < i && 0 <= j < n && k != j ==>
                #[trigger] result@[k * n + j] == 0.0f32,
            // Diagonal elements in processed rows (k < i) are set.
            forall|k: int|
                0 <= k < i ==>
                #[trigger] result@[k * n + k] == v@[k],
            // All elements in unprocessed rows (k >= i) are zero.
            forall|k: int, j: int|
                i <= k < n && 0 <= j < n ==>
                #[trigger] result@[k * n + j] == 0.0f32,
        decreases n - i,
    {
        proof {
            let old_result = result@;
            assert(forall|k: int, j: int| i <= k < n && 0 <= j < n ==> old_result[k * n + j] == 0.0f32);
            result.set(i * n + i, v[i]);
            assert(forall|k: int, j: int| i + 1 <= k < n && 0 <= j < n ==> result@[k * n + j] == 0.0f32) by {
                assert forall|k: int, j: int| i + 1 <= k < n && 0 <= j < n implies result@[k * n + j] == old_result[k * n + j] by {
                    assert(k * n + j != i * n + i);
                }
            };
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}