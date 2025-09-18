// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed exp parameter from int to usize to avoid casting in exec code */
fn pow(base: f32, exp: usize) -> (r: f32)
    requires exp >= 0
    decreases exp
{
    if exp == 0 { 1.0f32 } else { base * pow(base, exp - 1) }
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
/* code modified by LLM (iteration 5): Removed as int casts and passed usize directly to pow */
{
    let mut result = Vec::with_capacity(x.len());
    for k in 0..x.len() {
        let xk = x[k];
        let yk = y[k];
        let mut val = 0.0f32;
        for i in 0..c.len() {
            for j in 0..c[i].len() {
                val = val + c[i][j] * pow(xk, i) * pow(yk, j);
            }
        }
        result.push(val);
    }
    result
}
// </vc-code>

}
fn main() {}