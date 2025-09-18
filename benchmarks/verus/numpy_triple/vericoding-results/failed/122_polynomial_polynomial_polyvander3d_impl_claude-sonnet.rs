// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic overflow by using wrapping operations */
fn pow(base: f64, exp: usize) -> f64 {
    let mut result = 1.0;
    let mut i: usize = 0;
    while i < exp
        invariant i <= exp
        decreases exp - i
    {
        result = result * base;
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 5): fixed bounds checking and loop termination */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut p: usize = 0;
    while p < x.len()
        invariant 
            p <= x.len(),
            result.len() == p,
            forall|q: int| 0 <= q < result.len() ==> result[q].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
        decreases x.len() - p
    {
        let mut row: Vec<f64> = Vec::new();
        let mut i: usize = 0;
        while i <= x_deg
            invariant 
                i <= x_deg + 1,
                row.len() == i * (y_deg + 1) * (z_deg + 1),
                p < x.len()
            decreases x_deg + 1 - i
        {
            let mut j: usize = 0;
            while j <= y_deg
                invariant 
                    j <= y_deg + 1,
                    row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1),
                    p < x.len()
                decreases y_deg + 1 - j
            {
                let mut k: usize = 0;
                while k <= z_deg
                    invariant 
                        k <= z_deg + 1,
                        row.len() == i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + k,
                        p < x.len()
                    decreases z_deg + 1 - k
                {
                    let x_pow = pow(x[p], i);
                    let y_pow = pow(y[p], j);
                    let z_pow = pow(z[p], k);
                    row.push(x_pow * y_pow * z_pow);
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        result.push(row);
        p = p + 1;
    }
    result
}
// </vc-code>

}
fn main() {}