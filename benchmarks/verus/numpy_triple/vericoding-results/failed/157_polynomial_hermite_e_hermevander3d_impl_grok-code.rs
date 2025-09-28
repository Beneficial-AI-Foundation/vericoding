// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn hermite_poly_exec(k: usize, t: f64) -> (r: f64)
    decreases k
    ensures
        r == hermite_poly(k as int, t)
{
    if k == 0 {
        1.0
    } else if k == 1 {
        t
    } else {
        let h_prev2 = hermite_poly_exec(k - 2, t);
        let h_prev1 = hermite_poly_exec(k - 1, t);
        t * h_prev1 - ((k - 1) as f64) * h_prev2
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
/* code modified by LLM (iteration 2): implemented computation using exec helper for Hermite E polynomials with proper Vec access */
{
    let deg_x = deg[0] as usize;
    let deg_y = deg[1] as usize;
    let deg_z = deg[2] as usize;
    let mut result: Vec<Vec<f64>> = Vec::new();
    for p in 0..x.len() {
        let mut row: Vec<f64> = Vec::new();
        for ix in 0..=deg_x {
            for iy in 0..=deg_y {
                for iz in 0..=deg_z {
                    let hx = hermite_poly_exec(ix, x[p]);
                    let hy = hermite_poly_exec(iy, y[p]);
                    let hz = hermite_poly_exec(iz, z[p]);
                    let val = hx * hy * hz;
                    row.push(val);
                }
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}