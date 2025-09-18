// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added trigger to forall in ensures clause */
fn polyval1d(c: &Vec<f32>, x: f32) -> (res: f32)
    requires c.len() > 0
    ensures
        c.len() == 1 ==> res == c[0],
        (forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i] == 0.0f32) ==> res == 0.0f32,
        x == 0.0f32 ==> res == c[0],
{
    let mut res = 0.0f32;
    let mut i = c.len();
    while i > 0
        decreases i
    {
        i = i - 1;
        res = res * x + c[i];
    }
    res
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
    /* code modified by LLM (iteration 2): added triggers to forall in outer loop invariant */
    let mut result: Vec<f32> = Vec::new();
    let mut k: usize = 0;
    while k < x.len()
        invariant
            0 <= k <= x.len(),
            result.len() == k,
            x.len() == y.len(),
            c.len() > 0,
            forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() > 0,
            forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() == c[0].len(),
            (c.len() == 1 && c[0].len() == 1) ==> (forall|j: int| 0 <= j < k ==> result[j] == c[0][0]),
            (forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j] == 0.0f32) ==> 
                (forall|j: int| 0 <= j < k ==> result[j] == 0.0f32),
            forall|j: int| 0 <= j < k && x[j] == 0.0f32 && y[j] == 0.0f32 ==> result[j] == c[0][0]
        decreases x.len() - k
    {
        let mut p_y: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < c.len()
            decreases c.len() - i
        {
            let pi_y = polyval1d(&c[i], y[k]);
            p_y.push(pi_y);
            i = i + 1;
        }

        let val = polyval1d(&p_y, x[k]);
        result.push(val);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}