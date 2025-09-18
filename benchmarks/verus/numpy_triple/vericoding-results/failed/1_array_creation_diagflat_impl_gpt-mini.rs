// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide zero_f32 and idx helpers for indexing */
spec fn zero_f32() -> f32 { 0.0f32 }
spec fn idx(n: nat, i: nat, j: nat) -> nat { i * n + j }
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
    /* code modified by LLM (iteration 5): implement nested loops with nat indices and invariants proving placement of diagonal elements and zeros */
    let n: nat = v.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i: nat = 0usize;
    while i < n
        invariant i <= n
        invariant result.len() == i * n
        invariant forall |r: nat, c: nat| r < i && c < n ==> result[r * n + c] == if r == c { v[r] } else { 0.0f32 }
        decreases n - i
    {
        let mut j: nat = 0usize;
        while j < n
            invariant j <= n
            invariant result.len() == i * n + j
            invariant forall |r: nat, c: nat| r < i && c < n ==> result[r * n + c] == if r == c { v[r] } else { 0.0f32 }
            invariant forall |c: nat| c < j ==> result[i * n + c] == if i == c { v[i] } else { 0.0f32 }
            decreases n - j
        {
            if i == j {
                result.push(v[i]);
            } else {
                result.push(0.0f32);
            }
            j = j + 1usize;
        }
        i = i + 1usize;
    }
    result
}
// </vc-code>

}
fn main() {}