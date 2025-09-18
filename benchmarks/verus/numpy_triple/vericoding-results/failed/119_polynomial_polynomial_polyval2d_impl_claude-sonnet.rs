// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches by casting to int */
exec fn power_f32_exec(base: f32, exp: usize) -> f32 {
    let mut result = 1.0f32;
    let mut i = 0;
    while i < exp
        invariant
            i <= exp,
        decreases exp - i
    {
        result = result * base;
        i = i + 1;
    }
    result
}

fn eval_polynomial_2d_point(x_val: f32, y_val: f32, c: &Vec<Vec<f32>>) -> f32 {
    let mut result = 0.0f32;
    let mut i = 0;
    while i < c.len()
        invariant
            i <= c.len(),
        decreases c.len() - i
    {
        let mut j = 0;
        while j < c[i as int].len()
            invariant
                j <= c[i as int].len(),
            decreases c[i as int].len() - j
        {
            let term = c[i as int][j] * power_f32_exec(x_val, i) * power_f32_exec(y_val, j);
            result = result + term;
            j = j + 1;
        }
        i = i + 1;
    }
    result
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
/* code modified by LLM (iteration 5): using exec helper function with proper decreases clauses */
{
    let mut result = Vec::new();
    let mut k = 0;
    while k < x.len()
        invariant
            result.len() == k,
            k <= x.len(),
            x.len() == y.len(),
        decreases x.len() - k
    {
        let val = eval_polynomial_2d_point(x[k], y[k], &c);
        result.push(val);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}