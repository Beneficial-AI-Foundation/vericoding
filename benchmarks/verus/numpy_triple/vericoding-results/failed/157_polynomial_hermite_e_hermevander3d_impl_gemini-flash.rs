// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [brief description] */
spec fn hermite_poly_f64(k: nat, t: f64) -> f64
    decreases k
{
    if k == 0 {
        1.0
    } else if k == 1 {
        t
    } else if k > 1 {
        t * hermite_poly_f64((k - 1) as nat, t) - (k - 1) as f64 * hermite_poly_f64((k - 2) as nat, t)
    } else {
        1.0 // Should not be reached with proper usage (k >= 0)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_poly(k: int, t: f64) -> f64
    decreases k
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        t
    } else {

        1.0
    }
}

fn hermevander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, deg: Vec<u8>) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        deg.len() == 3,
        deg[0] as int >= 0 && deg[1] as int >= 0 && deg[2] as int >= 0,
    ensures
        result.len() == x.len(),
        forall |p: int| 0 <= p < result.len() ==> {
            let x_deg = deg[0] as int;
            let y_deg = deg[1] as int; 
            let z_deg = deg[2] as int;
            let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
            &&& #[trigger] result[p].len() == order
            &&& (order > 0 ==> result[p][0] == 1.0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Removed direct `as int` casts for `k_x`, `k_y`, `k_z` after arithmetic operations on `usize` to align with `nat` type used in `hermite_poly_f64` helper. Changed `x_deg`, `y_deg`, `z_deg` to `usize` for `order` calculation */
{
    let N = x.len();
    let x_deg: usize = deg[0] as usize;
    let y_deg: usize = deg[1] as usize;
    let z_deg: usize = deg[2] as usize;
    let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);

    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut p_idx: usize = 0;

    while p_idx < N
    invariant
        p_idx <= N,
        result.len() == p_idx,
        forall |i: int| 0 <= i && (i as usize) < p_idx ==> {
            &&& result[i as usize].len() == order
            &&& (order > 0 ==> result[i as usize][0] == 1.0)
        }
    {
        let mut row: Vec<f64> = Vec::new();
        let mut col_idx: usize = 0;

        while col_idx < order
        invariant
            col_idx <= order,
            row.len() == col_idx,
            forall |c_idx: int| 0 <= c_idx && (c_idx as usize) < col_idx ==> {
                true
            }
        {
            let mut current_col_val: f64 = 1.0;
            let mut temp_col_idx: usize = col_idx;

            let k_z = temp_col_idx % (z_deg + 1);
            temp_col_idx = temp_col_idx / (z_deg + 1);
            let k_y = temp_col_idx % (y_deg + 1);
            temp_col_idx = temp_col_idx / (y_deg + 1);
            let k_x = temp_col_idx;


            if k_x <= x_deg {
                current_col_val *= hermite_poly_f64(k_x as nat, x[p_idx]);
            }
            if k_y <= y_deg {
                current_col_val *= hermite_poly_f64(k_y as nat, y[p_idx]);
            }
            if k_z <= z_deg {
                current_col_val *= hermite_poly_f64(k_z as nat, z[p_idx]);
            }

            row.push(current_col_val);
            col_idx = col_idx + 1;
        }
        result.push(row);
        p_idx = p_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}