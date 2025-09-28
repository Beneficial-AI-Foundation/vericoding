// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added named return value for ensures clause */
fn pow_f64(base: f64, exp: usize) -> (result: f64)
    requires
        exp <= usize::MAX,
    ensures
        true,
{
    let mut result = 1.0;
    let mut i = 0;
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
    /* code modified by LLM (iteration 5): removed invalid requires statements from method body */
    let n = x.len();
    
    let total_terms = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
    let mut result: Vec<Vec<f64>> = Vec::new();
    
    let mut row_idx = 0;
    while row_idx < n
        invariant
            row_idx <= n,
            result@.len() == row_idx,
            forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == total_terms,
        decreases n - row_idx
    {
        let mut row: Vec<f64> = Vec::new();
        
        let mut k = 0;
        while k <= z_deg
            invariant
                k <= z_deg + 1,
                row@.len() == k * (x_deg + 1) * (y_deg + 1),
                row_idx < n,
            decreases z_deg + 1 - k
        {
            let mut j = 0;
            while j <= y_deg
                invariant
                    j <= y_deg + 1,
                    row@.len() == k * (x_deg + 1) * (y_deg + 1) + j * (x_deg + 1),
                    row_idx < n,
                decreases y_deg + 1 - j
            {
                let mut i = 0;
                while i <= x_deg
                    invariant
                        i <= x_deg + 1,
                        row@.len() == k * (x_deg + 1) * (y_deg + 1) + j * (x_deg + 1) + i,
                        row_idx < n,
                    decreases x_deg + 1 - i
                {
                    let x_pow = pow_f64(x[row_idx], i);
                    let y_pow = pow_f64(y[row_idx], j);
                    let z_pow = pow_f64(z[row_idx], k);
                    let term = x_pow * y_pow * z_pow;
                    row.push(term);
                    i = i + 1;
                }
                j = j + 1;
            }
            k = k + 1;
        }
        
        result.push(row);
        row_idx = row_idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}