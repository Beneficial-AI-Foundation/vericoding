// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper to expose Vec len as int */
spec fn vlen_as_int<T>(v: Vec<T>) -> int {
    v.len()
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
    /* code modified by LLM (iteration 5): use int loop counters and cast to usize for indexing; maintain invariants */
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    let mut ix: int = 0;
    while ix < x.len()
        invariant
            result.len() == ix,
        decreases
            x.len() - ix
    {
        let mut row: Vec<Vec<f64>> = Vec::new();
        let mut iy: int = 0;
        while iy < y.len()
            invariant
                row.len() == iy,
            decreases
                y.len() - iy
        {
            let mut col: Vec<f64> = Vec::new();
            let mut iz: int = 0;
            while iz < z.len()
                invariant
                    col.len() == iz,
                decreases
                    z.len() - iz
            {
                let mut sum: f64 = 0.0;
                let mut i: int = 0;
                while i < c.len()
                    invariant
                        i <= c.len(),
                    decreases
                        c.len() - i
                {
                    let mut j: int = 0;
                    while j < c[i as usize].len()
                        invariant
                            j <= c[i as usize].len(),
                        decreases
                            c[i as usize].len() - j
                    {
                        let mut k: int = 0;
                        while k < c[i as usize][j as usize].len()
                            invariant
                                k <= c[i as usize][j as usize].len(),
                            decreases
                                c[i as usize][j as usize].len() - k
                        {
                            let ci = c[i as usize][j as usize][k as usize];
                            let tx = if i == 0 { 1.0 } else if i == 1 { x[ix as usize] } else { 0.0 };
                            let ty = if j == 0 { 1.0 } else if j == 1 { y[iy as usize] } else { 0.0 };
                            let tz = if k == 0 { 1.0 } else if k == 1 { z[iz as usize] } else { 0.0 };
                            sum = sum + ci * tx * ty * tz;
                            k += 1;
                        }
                        j += 1;
                    }
                    i += 1;
                }
                col.push(sum);
                iz += 1;
            }
            row.push(col);
            iy += 1;
        }
        result.push(row);
        ix += 1;
    }
    result
}

// </vc-code>


}
fn main() {}