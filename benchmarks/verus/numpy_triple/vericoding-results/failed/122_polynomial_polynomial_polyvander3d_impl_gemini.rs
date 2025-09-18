// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to power function */
fn power(base: f64, exp: usize) -> (res: f64) {
    let mut r = 1.0;
    let mut i = 0;
    while i < exp
        invariant i <= exp
        decreases exp - i
    {
        r = r * base;
        i = i + 1;
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
    /* code modified by LLM (iteration 3): added decreases clauses to all loops to prove termination */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let num_points = x.len();
    let mut p: usize = 0;

    while p < num_points
        invariant
            p <= num_points,
            result.len() == p,
            forall|i_p: int| 0 <= i_p < result.len() ==> 
                result[i_p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
        decreases num_points - p
    {
        let mut row = Vec::new();
        let xp = x[p];
        let yp = y[p];
        let zp = z[p];

        let mut i: usize = 0;
        while i <= x_deg
            invariant
                i <= x_deg + 1,
                row.len() == i * (y_deg + 1) * (z_deg + 1),
            decreases (x_deg + 1) - i
        {
            let mut j: usize = 0;
            while j <= y_deg
                invariant
                    j <= y_deg + 1,
                    row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1),
                decreases (y_deg + 1) - j
            {
                let mut k: usize = 0;
                while k <= z_deg
                    invariant
                        k <= z_deg + 1,
                        row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + k,
                    decreases (z_deg + 1) - k
                {
                    let val = power(xp, i) * power(yp, j) * power(zp, k);
                    row.push(val);
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
        result.push(row);
        p += 1;
    }
    result
}
// </vc-code>

}
fn main() {}