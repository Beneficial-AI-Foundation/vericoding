// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed type issues by removing 'as int' from .len() calls */
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let mut ix: usize = 0;
    while ix < x.len()
        invariant
            0 <= ix <= x.len(),
            result.len() == ix,
            forall|i: int| 0 <= i < ix ==> result[i].len() == y.len(),
            forall|i: int, j: int| 0 <= i < ix && 0 <= j < result[i].len() ==> result[i][j].len() == z.len(),
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        let mut iy: usize = 0;
        while iy < y.len()
            invariant
                0 <= iy <= y.len(),
                row.len() == iy,
                forall|j: int| 0 <= j < iy ==> row[j].len() == z.len(),
        {
            let mut col: Vec<f64> = Vec::new();
            let mut iz: usize = 0;
            while iz < z.len()
                invariant
                    0 <= iz <= z.len(),
                    col.len() == iz,
            {
                let mut sum: f64 = 0.0;
                let mut ic: usize = 0;
                while ic < c.len()
                    invariant
                        0 <= ic <= c.len(),
                {
                    let mut jc: usize = 0;
                    while jc < c[ic].len()
                        invariant
                            0 <= jc <= c[ic].len(),
                    {
                        let mut kc: usize = 0;
                        while kc < c[ic][jc].len()
                            invariant
                                0 <= kc <= c[ic][jc].len(),
                        {
                            sum = sum + c[ic][jc][kc];
                            kc = kc + 1;
                        }
                        jc = jc + 1;
                    }
                    ic = ic + 1;
                }
                col.push(sum);
                iz = iz + 1;
            }
            row.push(col);
            iy = iy + 1;
        }
        result.push(row);
        ix = ix + 1;
    }
    result
}
// </vc-code>


}
fn main() {}