// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected floating point literals and indexing of `Vec<f64>` to `usize` for `get()` and `set()`. */
fn legendre(x_val: f64, degree: usize) -> Vec<f64>
    ensures
        legendre(x_val, degree).len() == degree + 1,
        forall|i: int| 0 <= i && i < legendre(x_val, degree).len() ==> 
            legendre(x_val, degree).get(i) == 
                if i == 0 { 1.0_f64 }
                else if i == 1 { x_val }
                else {
                    ( (2.0_f64 * i as f64 - 1.0_f64) * x_val * legendre(x_val, degree).get((i - 1) as usize).unwrap() - (i as f64 - 1.0_f64) * legendre(x_val, degree).get((i - 2) as usize).unwrap() ) / (i as f64)
                }
{
    let mut p: Vec<f64> = Vec::new();
    p.push(1.0_f64);
    if degree >= 1 {
        p.push(x_val);
    }
    for i in 2..=degree {
        let val = ( (2.0_f64 * i as f64 - 1.0_f64) * x_val * p[i-1] - (i as f64 - 1.0_f64) * p[i-2]) / (i as f64);
        p.push(val);
    }
    p
}
// </vc-helpers>

// <vc-spec>
fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: usize, deg_y: usize) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x + 1) * (deg_y + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Using for loop with `0..x.len()` for iterating and corrected range for inner loops from `0..=deg` to `0..deg+1`. */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    for i_idx in 0..x.len() {
        let x_val = x[i_idx];
        let y_val = y[i_idx];

        let px = legendre(x_val, deg_x);
        let py = legendre(y_val, deg_y);

        let mut row: Vec<f64> = Vec::new();
        // The capacity is known, so we resize the vector after creation.
        row.resize((deg_x + 1) * (deg_y + 1), 0.0);

        for j_idx in 0..deg_x + 1 {
            for k_idx in 0..deg_y + 1 {
                let index = j_idx * (deg_y + 1) + k_idx;
                row.set(index, px[j_idx] * py[k_idx]);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}