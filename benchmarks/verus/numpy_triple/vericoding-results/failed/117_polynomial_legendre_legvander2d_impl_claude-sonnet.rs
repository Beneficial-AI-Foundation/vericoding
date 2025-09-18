// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int first to avoid direct usize to f64 cast */
fn compute_legendre_value(n: usize, x: f64) -> (result: f64)
    ensures n == 0 ==> result == 1.0
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        let mut p0 = 1.0;
        let mut p1 = x;
        let mut i = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                i == 2 ==> (p0 == 1.0 && p1 == x)
        {
            let i_int = i as int;
            let coeff1 = (2 * i_int - 1) as f64;
            let coeff2 = (i_int - 1) as f64;
            let divisor = i_int as f64;
            let p_new = (coeff1 * x * p1 - coeff2 * p0) / divisor;
            p0 = p1;
            p1 = p_new;
            i += 1;
        }
        p1
    }
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
{
    /* code modified by LLM (iteration 5): convert usize to int first to avoid direct usize to f64 cast */
    let n_points = x.len();
    let n_terms = (deg_x + 1) * (deg_y + 1);
    let mut result: Vec<Vec<f64>> = Vec::new();
    
    let mut point_idx = 0;
    while point_idx < n_points
        invariant
            0 <= point_idx <= n_points,
            result.len() == point_idx,
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == n_terms,
            forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j = 0;
        
        while j <= deg_y
            invariant
                0 <= j <= deg_y + 1,
                row.len() == j * (deg_x + 1),
                j == 0 ==> row.len() == 0,
                j > 0 && row.len() > 0 ==> row[0] == 1.0
        {
            let mut i = 0;
            while i <= deg_x
                invariant
                    0 <= i <= deg_x + 1,
                    row.len() == j * (deg_x + 1) + i,
                    j == 0 && i == 1 && row.len() > 0 ==> row[0] == 1.0
            {
                let leg_x = compute_legendre_value(i, x[point_idx]);
                let leg_y = compute_legendre_value(j, y[point_idx]);
                let value = leg_x * leg_y;
                row.push(value);
                i += 1;
            }
            j += 1;
        }
        
        result.push(row);
        point_idx += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}