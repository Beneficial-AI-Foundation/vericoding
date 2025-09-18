// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute pow for f64 */
fn pow_f64(a: f64, n: usize) -> f64 {
    let mut r: f64 = 1.0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        decreases n - i
    {
        r = r * a;
        i += 1;
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|p: int| 0 <= p < result.len() ==> result[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build 3D Vandermonde rows with correct invariants */
    let n: usize = x.len();
    let cols: usize = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut p: usize = 0;
    while p < n
        invariant p <= n
        invariant result.len() == p
        decreases n - p
    {
        let mut row: Vec<f64> = Vec::new();
        let mut i: usize = 0;
        while i <= x_deg
            invariant i <= x_deg + 1
            invariant row.len() == i * (y_deg + 1) * (z_deg + 1)
            decreases (x_deg + 1) - i
        {
            let xp: f64 = pow_f64(x@[p], i);
            let mut j: usize = 0;
            while j <= y_deg
                invariant j <= y_deg + 1
                invariant row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1)
                decreases (y_deg + 1) - j
            {
                let yjp: f64 = pow_f64(y@[p], j);
                let mut k: usize = 0;
                while k <= z_deg
                    invariant k <= z_deg + 1
                    invariant row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + k
                    decreases (z_deg + 1) - k
                {
                    let zkp: f64 = pow_f64(z@[p], k);
                    row.push(xp * yjp * zkp);
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        proof {
            assert(row.len() == cols);
        }
        result.push(row);
        p += 1;
    }
    result
}
// </vc-code>

}
fn main() {}