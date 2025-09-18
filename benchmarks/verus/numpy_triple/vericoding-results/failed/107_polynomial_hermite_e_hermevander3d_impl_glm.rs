// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix int_to_f64 conversion and type issues */
fn hermite_poly_impl(k: int, t: f64) -> f64
    decreases k
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        t
    } else {
        2.0 * t * hermite_poly_impl(k - 1, t) - 2.0 * (k - 1 as f64) * hermite_poly_impl(k - 2, t)
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

fn hermevander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, deg: Vec<int>) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        deg.len() == 3,
        deg[0] >= 0 && deg[1] >= 0 && deg[2] >= 0,
    ensures
        result.len() == x.len(),
        forall |p: int| 0 <= p < result.len() ==> {
            let x_deg = deg[0];
            let y_deg = deg[1]; 
            let z_deg = deg[2];
            let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
            &&& #[trigger] result[p].len() == order
            &&& (order > 0 ==> result[p][0] == 1.0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix int to nat conversions and for loop ranges */
{
    let dx = deg[0];
    let dy = deg[1];
    let dz = deg[2];
    let n = x.len();
    let mut result = Vec::with_capacity(n);

    for i in 0..n {
        let mut x_vals = Vec::with_capacity((dx + 1) as nat);
        for kx in 0..=dx as nat {
            x_vals.push(hermite_poly_impl(kx as int, x[i]));
        }

        let mut y_vals = Vec::with_capacity((dy + 1) as nat);
        for ky in 0..=dy as nat {
            y_vals.push(hermite_poly_impl(ky as int, y[i]));
        }

        let mut z_vals = Vec::with_capacity((dz + 1) as nat);
        for kz in 0..=dz as nat {
            z_vals.push(hermite_poly_impl(kz as int, z[i]));
        }

        let order = (dx + 1) * (dy + 1) * (dz + 1);
        let mut point_result = Vec::with_capacity(order as nat);
        for kx in 0..=dx as nat {
            for ky in 0..=dy as nat {
                for kz in 0..=dz as nat {
                    let val = x_vals[kx] * y_vals[ky] * z_vals[kz];
                    point_result.push(val);
                }
            }
        }
        result.push(point_result);
    }

    result
}
// </vc-code>

}
fn main() {}