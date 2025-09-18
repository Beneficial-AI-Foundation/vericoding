// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove f32 powf operations and use ghost integer math */
proof fn polyval2d_helper_1(x: Seq<f32>, y: Seq<f32>, c: Seq<Seq<f32>>, i: int, j: int) -> (result: f32)
    requires
        0 <= i < c.len(),
        0 <= j < c[i].len(),
    ensures
        result == c[i][j]
{
    c[i][j]
}

proof fn polyval2d_helper_2(x: Seq<f32>, y: Seq<f32>, c: Seq<Seq<f32>>, k: int, cx: int, cy: int) -> (result: f32)
    requires
        0 <= k < x.len(),
        0 <= cx < c.len(),
        0 <= cy < c[cx].len(),
    ensures
        result == (if cx == 0 {1.0f32} else {x[k] * result}) * (if cy == 0 {1.0f32} else {y[k] * result}) * c[cx][cy]
{
    x[0] * y[0] * c[0][0]
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
/* code modified by LLM (iteration 5): replace f32 powf with manual exponentiation using loops */
{
    let mut result: Vec<f32> = Vec::new();
    let n = x.len();
    let m = c.len();
    let n2 = c[0].len();
    
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k,
    {
        let mut total: f32 = 0.0f32;
        let mut i: usize = 0;
        while i < m
            invariant
                i <= m,
        {
            let mut j: usize = 0;
            while j < n2
                invariant
                    j <= n2,
            {
                let mut x_pow: f32 = 1.0f32;
                let mut cx: usize = 0;
                while cx < i
                    invariant
                        cx <= i,
                {
                    x_pow = x_pow * x[k];
                    cx = cx + 1;
                }
                
                let mut y_pow: f32 = 1.0f32;
                let mut cy: usize = 0;
                while cy < j
                    invariant
                        cy <= j,
                {
                    y_pow = y_pow * y[k];
                    cy = cy + 1;
                }
                
                total = total + x_pow * y_pow * c[i][j];
                j = j + 1;
            }
            i = i + 1;
        }
        result.push(total);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}