// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type of `exp` to `usize` in ensures clause. */
pub fn power(base: f64, exp: usize) -> (result: f64)
    ensures
        (exp == 0 ==> result == 1.0) &&
        (exp > 0 ==> result == base * power(base, exp - 1))
{
    if exp == 0 {
        1.0
    } else {
        base * power(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x@.len() == y@.len(),
        y@.len() == z@.len(),
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type of `p_idx` and `k` to `int` in `invariant` clauses for `result@.len()` checks. */
{
    let num_points = x.len();
    let num_terms = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);

    let mut result: Vec<Vec<f64>> = Vec::new();
    result.reserve(num_points);

    let mut p_idx: usize = 0;
    while p_idx < num_points
        invariant
            p_idx <= num_points,
            result@.len() == p_idx as int,
            forall|k: int| 0 <= k && k < p_idx ==> result@[k].len() == num_terms as nat,
        decreases num_points - p_idx
    {
        let curr_x = x[p_idx];
        let curr_y = y[p_idx];
        let curr_z = z[p_idx];

        let mut point_poly_values: Vec<f64> = Vec::new();
        point_poly_values.reserve(num_terms);

        let mut i: usize = 0;
        while i <= x_deg
            invariant
                i <= x_deg + 1,
                point_poly_values@.len() == (i * (y_deg + 1) * (z_deg + 1)) as nat,
            decreases x_deg + 1 - i
        {
            let mut j: usize = 0;
            while j <= y_deg
                invariant
                    j <= y_deg + 1,
                    point_poly_values@.len() == ((i * (y_deg + 1) + j) * (z_deg + 1)) as nat,
                decreases y_deg + 1 - j
            {
                let mut k: usize = 0;
                while k <= z_deg
                    invariant
                        k <= z_deg + 1,
                        point_poly_values@.len() == ((i * (y_deg + 1) + j) * (z_deg + 1) + k) as nat,
                    decreases z_deg + 1 - k
                {
                    let term = power(curr_x, i) * power(curr_y, j) * power(curr_z, k);
                    point_poly_values.push(term);
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        result.push(point_poly_values);
        p_idx = p_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}