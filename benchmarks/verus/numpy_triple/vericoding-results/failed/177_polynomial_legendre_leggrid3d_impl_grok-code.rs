// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn lagrange_at_x(x: & Vec<f64>, k0: usize, val: f64) -> f64
    requires 0 <= k0 < (*x).len(),
{
    let x_len = (*x).len();
    let mut num = 1.0_f64;
    let mut den = 1.0_f64;
    for l in 0..x_len {
        if l != k0 {
            num = num * (val - (*x)[l]);
            den = den * ((*x)[k0] - (*x)[l]);
        }
    }
    if den == 0.0_f64 {
        0.0_f64
    } else {
        num / den
    }
}

fn lagrange_at_y(y: & Vec<f64>, k0: usize, val: f64) -> f64
    requires 0 <= k0 < (*y).len(),
{
    let y_len = (*y).len();
    let mut num = 1.0_f64;
    let mut den = 1.0_f64;
    for l in 0..y_len {
        if l != k0 {
            num = num * (val - (*y)[l]);
            den = den * ((*y)[k0] - (*y)[l]);
        }
    }
    if den == 0.0_f64 {
        0.0_f64
    } else {
        num / den
    }
}

/* helper modified by LLM (iteration 4): Changed k0 to usize and updated invariants to fix type errors */
fn lagrange_at_z(z: & Vec<f64>, k0: usize, val: f64) -> f64
    requires 0 <= k0 < (*z).len(),
{
    let z_len = (*z).len();
    let mut num = 1.0_f64;
    let mut den = 1.0_f64;
    for l in 0..z_len {
        if l != k0 {
            num = num * (val - (*z)[l]);
            den = den * ((*z)[k0] - (*z)[l]);
        }
    }
    if den == 0.0_f64 {
        0.0_f64
    } else {
        num / den
    }
}
// </vc-helpers>

// <vc-spec>
fn leggrid3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, c: Vec<Vec<Vec<f64>>>) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x@.len() > 0,
        y@.len() > 0,
        z@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures

        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z@.len(),

        forall|i1: int, i2: int, j1: int, j2: int, k1: int, k2: int|
            0 <= i1 < x@.len() && 0 <= i2 < x@.len() && 
            0 <= j1 < y@.len() && 0 <= j2 < y@.len() &&
            0 <= k1 < z@.len() && 0 <= k2 < z@.len() ==>
            ((i1 != i2 || j1 != j2 || k1 != k2) ==> 
             (result@[i1][j1][k1] != result@[i2][j2][k2] || 
              (x@[i1] == x@[i2] && y@[j1] == y@[j2] && z@[k1] == z@[k2])))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation by using executable values x[i], y[j], z[k] instead of ghost sequence access */
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let x_len = x@.len() as usize;
    let y_len = y@.len() as usize;
    let z_len = z@.len() as usize;
    for i in 0..x_len {
        let mut result_i: Vec<Vec<f64>> = Vec::new();
        for j in 0..y_len {
            let mut result_j: Vec<f64> = Vec::new();
            for k in 0..z_len {
                let mut val = 0.0_f64;
                for i0 in 0..x_len {
                    for j0 in 0..y_len {
                        for k0 in 0..z_len {
                            let lx = lagrange_at_x(&x, i0, x[i]);
                            let ly = lagrange_at_y(&y, j0, y[j]);
                            let lz = lagrange_at_z(&z, k0, z[k]);
                            val = val + (*c)[i0][j0][k0] * lx * ly * lz;
                        }
                    }
                }
                result_j.push(val);
            }
            result_i.push(result_j);
        }
        result.push(result_i);
    }
    result
}
// </vc-code>

}
fn main() {}