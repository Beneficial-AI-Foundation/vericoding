// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Concrete implementation of Chebyshev polynomial, duplicate spec fn removed */
fn chebyshev_fn(n: usize, x: f64) -> f64
    decreases n
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        2.0 * x * chebyshev_fn(n - 1, x) - chebyshev_fn(n - 2, x)
    }
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
/* code modified by LLM (iteration 5): Nested loop implementation for 3D Chebyshev grid evaluation */
{
    let mut result: Vec<Vec<Vec<f64>>> = Vec::new();
    for ix in 0..x.len() {
        let mut iy_list: Vec<Vec<f64>> = Vec::new();
        for iy in 0..y.len() {
            let mut iz_list: Vec<f64> = Vec::new();
            for iz in 0..z.len() {
                let mut sum: f64 = 0.0;
                for i in 0..c.len() {
                    let ti: f64 = chebyshev_fn(i, x[ix]);
                    for j in 0..c[i].len() {
                        let tj: f64 = chebyshev_fn(j, y[iy]);
                        for k in 0..c[i][j].len() {
                            let tk: f64 = chebyshev_fn(k, z[iz]);
                            sum = sum + c[i][j][k] * ti * tj * tk;
                        }
                    }
                }
                iz_list.push(sum);
            }
            iy_list.push(iz_list);
        }
        result.push(iy_list);
    }
    result
}
// </vc-code>


}
fn main() {}