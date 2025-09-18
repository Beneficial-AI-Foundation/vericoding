// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed compilation errors about `nat` and `int` not being usable in `while` loop conditions. */
spec fn VerusExponent(base: f32, exp: u32) -> f32 {
    if exp == 0 {
        1.0f32
    } else {
        base * VerusExponent(base, exp.checked_sub(1).unwrap())
    }
}
spec fn mul_f32_vec_element_wise(a: Vec<f32>, b: Vec<f32>) -> Vec<f32>
    requires
        a.len() == b.len(),
    ensures
        mul_f32_vec_element_wise(a, b).len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> mul_f32_vec_element_wise(a, b)@[i] == a@[i] * b@[i],
{
    let mut result = Vec::new();
    result.reserve(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] * b@[j],
    {
        result.push(a[i] * b[i]);
        i = i + 1;
    }
    result
}

spec fn add_f32_vec_all_elements(v: Vec<f32>) -> f32
    ensures
        v.len() == 0 ==> add_f32_vec_all_elements(v) == 0.0f32,
        v.len() == 1 ==> add_f32_vec_all_elements(v) == v@[0],
        v.len() > 1 ==> add_f32_vec_all_elements(v) == v@[0] + add_f32_vec_all_elements(v.subsequence(1, v.len())),
{
    if v.len() == 0 {
        0.0f32
    } else if v.len() == 1 {
        v[0]
    } else {
        v[0] + add_f32_vec_all_elements(v.subsequence(1, v.len()))
    }
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
/* code modified by LLM (iteration 5): removed compilation errors about `nat` and `int` not being usable in `while` loop conditions. */
{
    let m = c.len();
    let n = c[0].len();
    let num_points = x.len();

    let mut result = Vec::new();
    result.reserve(num_points);

    let mut k = 0;
    while k < num_points
        invariant
            0 <= k <= num_points,
            result.len() == k,
            result@.len() == k,
            x.len() == num_points,
            y.len() == num_points,
            c.len() == m,
            c[0].len() == n,
            forall|i: int| #![trigger c[i]] 0 <= i < m ==> c[i].len() == n,
    {
        let x_k = x[k];
        let y_k = y[k];

        let mut sum_val = 0.0f32;
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i as int <= m,
                sum_val == 
                    ({ 
                        let mut s = 0.0f32;
                        let mut idx_i: usize = 0;
                        while idx_i < (i as usize) {
                            let mut s_inner = 0.0f32;
                            let mut idx_j: usize = 0;
                            while idx_j < n {
                                s_inner = s_inner + c[idx_i][idx_j] * VerusExponent(x_k, idx_i as u32) * VerusExponent(y_k, idx_j as u32);
                                idx_j = idx_j + 1;
                            }
                            s = s + s_inner;
                            idx_i = idx_i + 1;
                        }
                        s
                    }),
                x.len() == num_points,
                y.len() == num_points,
                c.len() == m,
                c[0].len() == n,
                forall|idx_i: int| #![trigger c[idx_i]] 0 <= idx_i < m ==> c[idx_i].len() == n,
        {
            let mut row_sum = 0.0f32;
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j as int <= n,
                    row_sum == 
                        ({ 
                            let mut s = 0.0f32;
                            let mut idx_j: usize = 0;
                            while idx_j < (j as usize) {
                                s = s + c[i][idx_j] * VerusExponent(y_k, idx_j as u32);
                                idx_j = idx_j + 1;
                            }
                            s
                        }),
                    x.len() == num_points,
                    y.len() == num_points,
                    c.len() == m,
                    c[0].len() == n,
                    forall|idx_i: int| #![trigger c[idx_i]] 0 <= idx_i < m ==> c[idx_i].len() == n,
            {
                row_sum = row_sum + c[i][j] * VerusExponent(y_k, j as u32);
                j = j + 1;
            }
            sum_val = sum_val + VerusExponent(x_k, i as u32) * row_sum;
            i = i + 1;
        }
        result.push(sum_val);
        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}