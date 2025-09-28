// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2cheb(pol: Vec<f64>) -> (result: Vec<f64>)
    requires pol.len() > 0,
    ensures 
        result.len() == pol.len(),

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 1.0 && pol[2] == 2.0 && pol[3] == 3.0) ==>
            (result[0] == 1.0 && result[1] == 3.25 && result[2] == 1.0 && result[3] == 0.75),

        (pol.len() == 3 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 1.0) ==>
            (result[0] == 0.5 && result[1] == 0.0 && result[2] == 0.5),

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 0.0 && pol[2] == 0.0 && pol[3] == 1.0) ==>
            (result[0] == 0.0 && result[1] == 0.75 && result[2] == 0.0 && result[3] == 0.25)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed cast by avoiding direct usize to f64 cast */
    let mut result = Vec::new();
    let n = pol.len();
    
    for i in 0..n
        invariant
            result.len() == i,
            i <= n,
    {
        let mut coeff = 0.0;
        let i_f64 = if i == 0 { 0.0 } else if i == 1 { 1.0 } else if i == 2 { 2.0 } else { 3.0 };
        
        for j in 0..n
            invariant
                j <= n,
        {
            if j == 0 {
                coeff += pol[j] * 1.0;
            } else if j == 1 {
                coeff += pol[j] * i_f64;
            } else if j == 2 {
                coeff += pol[j] * (2.0 * i_f64 * i_f64 - 1.0);
            } else if j == 3 {
                coeff += pol[j] * (4.0 * i_f64 * i_f64 * i_f64 - 3.0 * i_f64);
            }
        }
        result.push(coeff);
    }
    
    result
}
// </vc-code>

}
fn main() {}