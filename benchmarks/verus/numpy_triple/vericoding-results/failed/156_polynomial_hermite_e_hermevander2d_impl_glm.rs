// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use i64 for intermediate arithmetic to avoid ghost code restrictions */
fn hermite_basis_exec(k: usize, t: i8) -> i8
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let k1 = k - 1;
        let k2 = k - 2;
        let h1 = hermite_basis_exec(k1, t) as i64;
        let h2 = hermite_basis_exec(k2, t) as i64;
        let k1_int = k1 as i64;
        let t_int = t as i64;
        let result = t_int * h1 - k1_int * h2;
        #[verifier::truncate]
        let truncated_result = result as i8;
        truncated_result
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(k: nat, t: int) -> int
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t)
    }
}

fn hermevander2d(x: Vec<i8>, y: Vec<i8>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|point_idx: int| 0 <= point_idx < result.len() ==> 
            result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): using fixed hermite_basis_exec helper */
{
    let num_points = x.len();
    let x_plus_one = x_deg.saturating_add(1);
    let y_plus_one = y_deg.saturating_add(1);
    let num_cols = x_plus_one.saturating_mul(y_plus_one);
    let mut result = Vec::with_capacity(num_points);
    
    for point_idx in 0..num_points {
        assert(point_idx < x.len() && point_idx < y.len());
        let x_val = x[point_idx];
        let y_val = y[point_idx];
        let mut row = Vec::with_capacity(num_cols);

        for i in 0..x_plus_one {
            for j in 0..y_plus_one {
                let h_x = hermite_basis_exec(i, x_val);
                let h_y = hermite_basis_exec(j, y_val);
                let value = h_x.wrapping_mul(h_y);
                row.push(value);
            }
        }

        result.push(row);
    }

    result
}
// </vc-code>

}
fn main() {}