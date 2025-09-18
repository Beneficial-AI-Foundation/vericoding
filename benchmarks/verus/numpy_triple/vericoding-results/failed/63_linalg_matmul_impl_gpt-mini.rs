// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns number of columns */
spec fn cols(V: Vec<Vec<f32>>) -> int
    requires V.len() > 0
{ V@[0].len() }
// </vc-helpers>

// <vc-spec>
fn matmul(A: Vec<Vec<f32>>, B: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires
        A.len() > 0,
        B.len() > 0,
        A@[0].len() == B.len(),
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A@[i].len() == A@[0].len(),
        forall|i: int| 0 <= i < B.len() ==> #[trigger] B@[i].len() == B@[0].len(),
    ensures
        result.len() == A.len(),
        result.len() > 0 ==> result@[0].len() == B@[0].len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == B@[0].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement matrix multiplication with nested loops and invariants */
    let m: int = A.len();
    let n: int = B.len();
    let p: int = B@[0].len();

    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: int = 0;
    while i < m
        invariant 0 <= i && i <= m;
        invariant result.len() == i;
        invariant forall|r: int| 0 <= r < result.len() ==> result@[r].len() == p;
        decreases m - i;
    {
        let mut row: Vec<f32> = Vec::new();

        let mut j: int = 0;
        while j < p
            invariant 0 <= j && j <= p;
            invariant row.len() == j;
            decreases p - j;
        {
            let mut sum: f32 = 0.0f32;

            let mut k: int = 0;
            while k < n
                invariant 0 <= k && k <= n;
                decreases n - k;
            {
                let av: f32 = A@[i]@[k];
                let bv: f32 = B@[k]@[j];
                sum = sum + av * bv;
                k = k + 1;
            }

            row.push(sum);
            j = j + 1;
        }

        result.push(row);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}