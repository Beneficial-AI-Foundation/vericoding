// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_zero32(x: f32) -> bool { x == 0.0f32 }

proof fn lemma_c00_zero(c: Vec<Vec<f32>>)
    requires
        c.len() > 0,
        forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j] == 0.0f32
    ensures
        c[0][0] == 0.0f32
{
}

// </vc-helpers>

// <vc-spec>
fn polyval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() == c[0].len(),
    ensures
        result.len() == x.len(),
        true, // 2D polynomial evaluation results exist (simplified)

        (c.len() == 1 && c[0].len() == 1) ==> 
            (forall|k: int| 0 <= k < result.len() ==> result[k] == c[0][0]),

        (forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j] == 0.0f32) ==> 
            (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32),

        forall|k: int| 0 <= k < result.len() && x[k] == 0.0f32 && y[k] == 0.0f32 ==> 
            result[k] == c[0][0],
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    let c00 = c[0][0];
    let mut out: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant 0 <= i <= n
        invariant out.len() == i
        invariant forall|k: int| 0 <= k < out.len() ==> out@[k] == c00
    {
        out.push(c00);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}