// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple row-major index for (i,j) in an n-by-n matrix */
spec fn diag_index(n: int, i: int, j: int) -> int { i * n + j }

/* helper modified by LLM (iteration 5): build flattened diagonal matrix sequence from vector view; uses int n and guards division by zero */
spec fn build_diagflat_seq(v: Seq<f32>) -> Seq<f32> {
    let n: int = v.len() as int;
    Seq::new(n * n, |k: int| {
        if n == 0 { 0.0f32 } else {
            let i = k / n;
            let j = k % n;
            if i == j { v[i] } else { 0.0f32 }
        }
    })
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
    /* code modified by LLM (iteration 5): construct the result directly from the specification sequence to avoid exec 'int' usage and ease verification */
    let res: Vec<f32> = Vec::from_seq(build_diagflat_seq(v@));
    res
}
// </vc-code>

}
fn main() {}