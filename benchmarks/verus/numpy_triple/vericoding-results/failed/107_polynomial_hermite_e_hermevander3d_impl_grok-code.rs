// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn hermite_poly(k: int, t: f64) -> f64
    requires k >= 0
    decreases k
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        2.0 * t
    } else {
        2.0 * t * hermite_poly(k - 1, t) - (((k - 1) as f64) * 2.0) * hermite_poly(k - 2, t)
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
{
    let mut result = Vec::new();
    let x_deg = deg[0];
    let y_deg = deg[1];
    let z_deg = deg[2];
    let len_p = x.len();
    let mut p = 0;
    while p < len_p
        invariant 0 <= p <= len_p
        invariant result.len() == p as nat
    {
        let mut poly_list = Vec::new();
        let mut ix = 0;
        while ix <= x_deg
            invariant 0 <= ix <= x_deg + 1
        {
            let hx = hermite_poly(ix, x[p]);
            let mut iy = 0;
            while iy <= y_deg
                invariant 0 <= iy <= y_deg + 1
            {
                let hy = hermite_poly(iy, y[p]);
                let mut iz = 0;
                while iz <= z_deg
                    invariant 0 <= iz <= z_deg + 1
                {
                    let hz = hermite_poly(iz, z[p]);
                    poly_list.push(hx * hy * hz);
                    iz += 1;
                }
                iy += 1;
            }
            ix += 1;
        }
        result.push(poly_list);
        p += 1;
    }
    result
}
// </vc-code>

}
fn main() {}