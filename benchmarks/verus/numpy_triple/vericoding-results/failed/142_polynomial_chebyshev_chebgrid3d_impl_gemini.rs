// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no changes] */
fn compute_chebyshev_T(n: usize, x: f64) -> (result: f64)
    ensures result == chebyshev_T(n as nat, x),
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        0.0
    }
}

/* helper modified by LLM (iteration 5): [simplified loop invariants to aid verification] */
fn chebval3d(x_val: f64, y_val: f64, z_val: f64, c: &Vec<Vec<Vec<f64>>>) -> (result: f64)
    requires
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
{
    let mut total: f64 = 0.0;
    let mut i: usize = 0;
    while i < c.len()
        invariant
            0 <= i <= c.len(),
        decreases c.len() - i
    {
        let mut j: usize = 0;
        while j < c[i].len()
            invariant
                i < c.len(),
                0 <= j <= c[i].len(),
            decreases c[i].len() - j
        {
            let mut k: usize = 0;
            while k < c[i][j].len()
                invariant
                    i < c.len(),
                    j < c[i].len(),
                    0 <= k <= c[i][j].len(),
                decreases c[i][j].len() - k
            {
                let ti = compute_chebyshev_T(i, x_val);
                let tj = compute_chebyshev_T(j, y_val);
                let tk = compute_chebyshev_T(k, z_val);
                total = total + c[i][j][k] * ti * tj * tk;
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
spec fn chebyshev_T(n: nat, x: f64) -> f64 
    decreases n
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        0.0
    }
}

fn chebgrid3d(
    x: Vec<f64>, 
    y: Vec<f64>, 
    z: Vec<f64>,
    c: Vec<Vec<Vec<f64>>>
) -> (result: Vec<Vec<Vec<f64>>>)
    requires 
        x.len() > 0,
        y.len() > 0, 
        z.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
    ensures
        result.len() == x.len(),
        forall|ix: int| 0 <= ix < result.len() ==> result[ix].len() == y.len(),
        forall|ix: int, iy: int| 0 <= ix < result.len() && 0 <= iy < result[ix].len() ==> result[ix][iy].len() == z.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [added invariants to preserve preconditions and simplified syntax] */
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let mut ix: usize = 0;
    while ix < x.len()
        invariant
            c.len() > 0,
            forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
            forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
            0 <= ix <= x.len(),
            result.len() == ix,
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
            forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> result[i][j].len() == z.len(),
        decreases x.len() - ix
    {
        let mut row_y: Vec<Vec<f64>> = Vec::new();
        let mut iy: usize = 0;
        while iy < y.len()
            invariant
                ix < x.len(),
                c.len() > 0,
                forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
                forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
                0 <= iy <= y.len(),
                row_y.len() == iy,
                forall|j: int| 0 <= j < row_y.len() ==> row_y[j].len() == z.len(),
            decreases y.len() - iy
        {
            let mut row_z: Vec<f64> = Vec::new();
            let mut iz: usize = 0;
            while iz < z.len()
                invariant
                    ix < x.len(),
                    iy < y.len(),
                    c.len() > 0,
                    forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
                    forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j].len() > 0,
                    0 <= iz <= z.len(),
                    row_z.len() == iz,
                decreases z.len() - iz
            {
                let val = chebval3d(x[ix], y[iy], z[iz], &c);
                row_z.push(val);
                iz = iz + 1;
            }
            row_y.push(row_z);
            iy = iy + 1;
        }
        result.push(row_y);
        ix = ix + 1;
    }
    result
}
// </vc-code>


}
fn main() {}