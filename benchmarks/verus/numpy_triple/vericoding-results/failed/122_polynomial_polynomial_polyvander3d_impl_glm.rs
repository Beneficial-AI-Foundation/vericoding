// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to loop */
exec fn pow_usize(base: f64, exp: usize) -> (result: f64)
    decreases exp
{
    if exp == 0 {
        1.0
    } else {
        let mut prod = base;
        let mut counter: usize = 1;
        while counter < exp
            invariant 1 <= counter <= exp
            decreases exp - counter
        {
            prod = prod * base;
            counter += 1;
        }
        prod
    }
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
    /* code modified by LLM (iteration 2): fixed inclusive ranges to exclusive ranges */
    let mut result = Vec::new();
    for p in 0..x.len() {
        let mut row = Vec::new();
        for i in 0..(x_deg+1) {
            for j in 0..(y_deg+1) {
                for k in 0..(z_deg+1) {
                    let term = pow_usize(x[p], i) * pow_usize(y[p], j) * pow_usize(z[p], k);
                    row.push(term);
                }
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}