// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix f32 multiplication and type issues */
spec fn pow(base: f32, exp: nat) -> f32
    decreases exp
{
    if exp == 0 {
        1.0f32
    } else {
        base.spec_mul(pow(base, (exp - 1) as nat))
    }
}

spec fn eval_poly_2d(x: f32, y: f32, c: Vec<Vec<f32>>) -> f32
{
    if c.len() == 0 || c[0].len() == 0 {
        0.0f32
    } else {
        eval_poly_2d_helper(x, y, c, 0, 0)
    }
}

spec fn eval_poly_2d_helper(x: f32, y: f32, c: Vec<Vec<f32>>, i: nat, j: nat) -> f32
    decreases c.len() - i, c[0].len() - j
{
    if i >= c.len() {
        0.0f32
    } else if j >= c[0].len() {
        eval_poly_2d_helper(x, y, c, (i + 1) as nat, 0)
    } else {
        c[i as int][j as int].spec_mul(pow(x, i as nat)).spec_mul(pow(y, j as nat)).spec_add(eval_poly_2d_helper(x, y, c, i, (j + 1) as nat))
    }
}

fn compute_pow(base: f32, exp: u32) -> (result: f32)
    ensures result == pow(base, exp as nat)
{
    if exp == 0 {
        1.0f32
    } else {
        let prev = compute_pow(base, exp - 1);
        base * prev
    }
}

fn eval_2d_polynomial(x_val: f32, y_val: f32, coeffs: &Vec<Vec<f32>>) -> (result: f32)
    requires
        coeffs.len() > 0,
        forall|i: int| 0 <= i < coeffs.len() ==> coeffs[i].len() > 0,
        forall|i: int| 0 <= i < coeffs.len() ==> coeffs[i].len() == coeffs[0].len()
    ensures result == eval_poly_2d(x_val, y_val, *coeffs)
{
    let mut sum: f32 = 0.0f32;
    let mut i: usize = 0;
    while i < coeffs.len()
        invariant
            0 <= i <= coeffs.len(),
            coeffs.len() > 0,
            forall|k: int| 0 <= k < coeffs.len() ==> coeffs[k].len() > 0,
            forall|k: int| 0 <= k < coeffs.len() ==> coeffs[k].len() == coeffs[0].len()
    {
        let mut j: usize = 0;
        while j < coeffs[i].len()
            invariant
                0 <= j <= coeffs[i].len(),
                0 <= i < coeffs.len(),
                coeffs.len() > 0,
                forall|k: int| 0 <= k < coeffs.len() ==> coeffs[k].len() > 0,
                forall|k: int| 0 <= k < coeffs.len() ==> coeffs[k].len() == coeffs[0].len()
        {
            let x_pow = compute_pow(x_val, i as u32);
            let y_pow = compute_pow(y_val, j as u32);
            sum = sum + coeffs[i][j] * x_pow * y_pow;
            j = j + 1;
        }
        i = i + 1;
    }
    sum
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
    /* code modified by LLM (iteration 5): implementation body for polyval2d */
    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < x.len()
        invariant
            0 <= k <= x.len(),
            result.len() == k,
            x.len() == y.len(),
            x.len() > 0,
            c.len() > 0,
            forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
            forall|i: int| 0 <= i < c.len() ==> c[i].len() == c[0].len(),
            forall|m: int| 0 <= m < k ==> result[m] == eval_poly_2d(x[m], y[m], c),
            (c.len() == 1 && c[0].len() == 1) ==> (forall|m: int| 0 <= m < k ==> result[m] == c[0][0]),
            (forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j] == 0.0f32) ==> (forall|m: int| 0 <= m < k ==> result[m] == 0.0f32),
            forall|m: int| 0 <= m < k && x[m] == 0.0f32 && y[m] == 0.0f32 ==> result[m] == c[0][0]
    {
        let val = eval_2d_polynomial(x[k], y[k], &c);
        result.push(val);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}