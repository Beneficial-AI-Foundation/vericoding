// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type mismatches in indexing and loop conditions by converting int indices to usize and lengths to int */
    let n = x.len();
    let mut result = Vec::new();
    let mut k = 0;
    while k < (n as int)
        decreases (n as int) - k
    {
        let mut x_powers = Vec::with_capacity(c.len());
        let mut x_power = 1.0f32;
        x_powers.push(x_power);
        let mut i_power = 1;
        while i_power < (c.len() as int)
            decreases (c.len() as int) - i_power
        {
            x_power = x_power * x[k as usize];
            x_powers.push(x_power);
            i_power = i_power + 1;
        }
        let mut y_powers = Vec::with_capacity(c[0].len());
        let mut y_power = 1.0f32;
        y_powers.push(y_power);
        let mut j_power = 1;
        while j_power < (c[0].len() as int)
            decreases (c[0].len() as int) - j_power
        {
            y_power = y_power * y[k as usize];
            y_powers.push(y_power);
            j_power = j_power + 1;
        }
        let mut sum = 0.0f32;
        let mut i = 0;
        while i < (c.len() as int)
            decreases (c.len() as int) - i
        {
            let mut j = 0;
            while j < (c[i as usize].len() as int)
                decreases (c[i as usize].len() as int) - j
            {
                sum = sum + c[i as usize][j as usize] * x_powers[i as usize] * y_powers[j as usize];
                j = j + 1;
            }
            i = i + 1;
        }
        result.push(sum);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}