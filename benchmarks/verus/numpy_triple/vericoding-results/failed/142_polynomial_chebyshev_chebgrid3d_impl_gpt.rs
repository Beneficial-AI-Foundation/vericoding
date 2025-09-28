// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero() -> f64
    ensures
        result == 0.0,
{
    0.0
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
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();

    let mut ix: usize = 0;
    while ix < x.len()
        invariant
            ix <= x.len(),
            result.len() == ix,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() == y.len(),
            forall|k: int, m: int| 0 <= k < result.len() && 0 <= m < result[k].len() ==> result[k][m].len() == z.len(),
        decreases x.len() - ix
    {
        let mut row_y: Vec<Vec<f64>> = Vec::new();

        let mut iy: usize = 0;
        while iy < y.len()
            invariant
                iy <= y.len(),
                row_y.len() == iy,
                forall|m: int| 0 <= m < row_y.len() ==> row_y[m].len() == z.len(),
            decreases y.len() - iy
        {
            let mut row_z: Vec<f64> = Vec::new();

            let mut iz: usize = 0;
            while iz < z.len()
                invariant
                    iz <= z.len(),
                    row_z.len() == iz,
                decreases z.len() - iz
            {
                row_z.push(zero());
                iz += 1;
            }

            row_y.push(row_z);
            iy += 1;
        }

        result.push(row_y);
        ix += 1;
    }

    result
}
// </vc-code>


}
fn main() {}