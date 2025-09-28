// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed exp parameter from nat to usize to fix compilation error with ghost type usage in exec code */
fn pow_f64(base: f64, exp: usize) -> f64
    decreases (exp as int)
{
    if exp == 0 {
        1.0
    } else {
        base * pow_f64(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x@.len() == y@.len(),
        y@.len() == z@.len(),
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed 'as nat' casts since pow_f64 now takes usize to fix ghost type error */
    let mut result: Vec<Vec<f64>> = Vec::with_capacity(x.len());
    let mut p = 0;
    while p < x.len()
        invariant
            result@.len() == p,
            forall|q: int| 0 <= q < p ==> result@[q].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
    {
        let mut row = Vec::with_capacity((x_deg + 1) * (y_deg + 1) * (z_deg + 1));
        let mut i = 0;
        while i <= x_deg
        {
            let mut j = 0;
            while j <= y_deg
            {
                let mut k = 0;
                while k <= z_deg
                {
                    let val = pow_f64(x[p], i) * pow_f64(y[p], j) * pow_f64(z[p], k);
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