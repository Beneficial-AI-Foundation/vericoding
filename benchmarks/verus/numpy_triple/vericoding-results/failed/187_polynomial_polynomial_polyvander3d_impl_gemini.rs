// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed exp type from nat to usize for exec compatibility */
fn pow(base: f64, exp: usize) -> (r: f64)
{
    let mut result: f64 = 1.0;
    let mut i: usize = 0;
    while i < exp
        invariant
            i <= exp,
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
        x@.len() == y@.len(),
        y@.len() == z@.len(),
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed 'as nat' cast to match modified pow helper */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut p: usize = 0;
    while p < x.len()
        invariant
            p <= x.len(),
            x@.len() == y@.len(),
            y@.len() == z@.len(),
            result@.len() == p,
            forall|k: int| 0 <= k < p ==> result@[k].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1),
        decreases x.len() - p
    {
        let mut row: Vec<f64> = Vec::new();
        let xp = x[p];
        let yp = y[p];
        let zp = z[p];

        let mut c: usize = 0;
        while c <= z_deg
            invariant
                p < x@.len(),
                c <= z_deg + 1,
                row@.len() == c * (x_deg + 1) * (y_deg + 1),
            decreases z_deg - c
        {
            let mut b: usize = 0;
            while b <= y_deg
                invariant
                    p < x@.len(),
                    c <= z_deg,
                    b <= y_deg + 1,
                    row@.len() == c * (x_deg + 1) * (y_deg + 1) + b * (x_deg + 1),
                decreases y_deg - b
            {
                let mut a: usize = 0;
                while a <= x_deg
                    invariant
                        p < x@.len(),
                        c <= z_deg,
                        b <= y_deg,
                        a <= x_deg + 1,
                        row@.len() == c * (x_deg + 1) * (y_deg + 1) + b * (x_deg + 1) + a,
                    decreases x_deg - a
                {
                    let x_pow = pow(xp, a);
                    let y_pow = pow(yp, b);
                    let z_pow = pow(zp, c);
                    row.push(x_pow * y_pow * z_pow);
                    a = a + 1;
                }
                b = b + 1;
            }
            c = c + 1;
        }
        result.push(row);
        p = p + 1;
    }
    result
}
// </vc-code>

}
fn main() {}