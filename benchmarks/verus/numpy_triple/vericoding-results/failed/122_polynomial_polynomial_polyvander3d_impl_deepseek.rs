// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unsupported powi function and added manual power calculation */
fn power(base: f64, exponent: usize) -> f64
    ensures exponent == 0 ==> result == 1.0
{
    if exponent == 0 {
        1.0
    } else {
        let mut result = 1.0;
        let mut count = 0;
        while count < exponent
            invariant count <= exponent, result == base.powi(count as i32)
        {
            result = result * base;
            count += 1;
        }
        result
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
/* code modified by LLM (iteration 5): replaced powi calls with manual power function */
{
    let n = x.len();
    let total_terms = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
    let mut result = Vec::<Vec<f64>>::new();
    
    let mut i = 0;
    while i < n
        invariant 
            i <= n,
            result.len() == i,
            forall|p: int| 0 <= p < i ==> result[p].len() == total_terms
    {
        let mut row = Vec::<f64>::new();
        let mut x_pow = 0;
        
        while x_pow <= x_deg
            invariant 
                x_pow <= x_deg + 1,
                row.len() == x_pow * (y_deg + 1) * (z_deg + 1)
        {
            let mut y_pow = 0;
            
            while y_pow <= y_deg
                invariant 
                    y_pow <= y_deg + 1,
                    row.len() == x_pow * (y_deg + 1) * (z_deg + 1) + y_pow * (z_deg + 1)
            {
                let mut z_pow = 0;
                
                while z_pow <= z_deg
                    invariant 
                        z_pow <= z_deg + 1,
                        row.len() == x_pow * (y_deg + 1) * (z_deg + 1) + y_pow * (z_deg + 1) + z_pow
                {
                    let x_val = power(x[i], x_pow);
                    let y_val = power(y[i], y_pow);
                    let z_val = power(z[i], z_pow);
                    let term = x_val * y_val * z_val;
                    row.push(term);
                    z_pow += 1;
                }
                y_pow += 1;
            }
            x_pow += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}