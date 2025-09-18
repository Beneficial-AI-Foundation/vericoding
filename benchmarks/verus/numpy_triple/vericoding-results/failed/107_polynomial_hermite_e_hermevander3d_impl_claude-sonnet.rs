// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed spec function syntax */
spec fn hermite_poly_helper(k: int, t: f64) -> f64
    decreases k
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        t
    } else {
        t * hermite_poly_helper(k - 1, t) - (k - 1) as f64 * hermite_poly_helper(k - 2, t)
    }
}

fn compute_hermite_basis(x_val: f64, y_val: f64, z_val: f64, x_deg: int, y_deg: int, z_deg: int) -> (result: Vec<f64>)
    requires x_deg >= 0, y_deg >= 0, z_deg >= 0
    ensures result.len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
    ensures result.len() > 0 ==> result[0] == 1.0
{
    let mut basis = Vec::new();
    let mut i = 0;
    while i <= x_deg
        invariant 0 <= i <= x_deg + 1
        invariant basis.len() == i * (y_deg + 1) * (z_deg + 1)
    {
        let mut j = 0;
        while j <= y_deg
            invariant 0 <= j <= y_deg + 1
            invariant basis.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1)
        {
            let mut k = 0;
            while k <= z_deg
                invariant 0 <= k <= z_deg + 1
                invariant basis.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + k
            {
                let val = hermite_poly_helper(i, x_val) * hermite_poly_helper(j, y_val) * hermite_poly_helper(k, z_val);
                basis.push(val);
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }
    basis
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
    /* code modified by LLM (iteration 5): fixed compilation error by adding proper braces around ensures */
    let mut result = Vec::new();
    let mut p = 0;
    
    while p < x.len()
        invariant 0 <= p <= x.len()
        invariant result.len() == p
        invariant forall |q: int| 0 <= q < p ==> {
            let x_deg = deg[0];
            let y_deg = deg[1];
            let z_deg = deg[2];
            let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
            &&& result[q].len() == order
            &&& (order > 0 ==> result[q][0] == 1.0)
        }
    {
        let x_val = x[p];
        let y_val = y[p];
        let z_val = z[p];
        let basis = compute_hermite_basis(x_val, y_val, z_val, deg[0], deg[1], deg[2]);
        result.push(basis);
        p += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}