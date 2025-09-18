// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added zeros function to initialize vector of zeros */
fn zeros(len: usize) -> Vec<f64>
    decreases len
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < len
        decreases len - i
    {
        v.push(0.0);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn poly2herm(pol: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == pol.len(),

        (forall|i: int| 0 <= i < pol.len() ==> pol[i] == 0.0) ==> 
            (forall|i: int| 0 <= i < result.len() ==> result[i] == 0.0),

        pol.len() > 0 ==> 
            (forall|i: int| 1 <= i < pol.len() ==> pol[i] == 0.0) ==>
                result[0] == pol[0],

        (pol.len() == 4 && pol[0] == 0.0 && pol[1] == 1.0 && 
         pol[2] == 2.0 && pol[3] == 3.0) ==>
            (result[0] == 1.0 && result[1] == 2.75 && 
             result[2] == 0.5 && result[3] == 0.375)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replaced vec![0.0; len] with zeros(len) to fix compilation error */
{
    let n = pol.len();
    if n == 0 {
        return vec![];
    }

    // Build the matrix M: n x n as 1D vector
    let mut M = zeros(n * n);
    // H0
    M[0 * n + 0] = 1.0;
    if n > 1 {
        M[1 * n + 1] = 2.0;
    }
    for j in 2..n {
        for i in 0..(j+1) {
            let mut coeff = 0.0;
            // Term from 2x * H_{j-1}: 
            if i >= 1 {
                coeff += 2.0 * M[(i-1) * n + (j-1)];
            }
            // Term from -2*(j-1)*H_{j-2}:
            if i <= j-2 {
                let mut float_coeff = 0.0;
                for _ in 0..(j-1) {
                    float_coeff += 1.0;
                }
                float_coeff *= 2.0;
                coeff -= float_coeff * M[i * n + (j-2)];
            }
            M[i * n + j] = coeff;
        }
    }

    // Solve for c: M * c = pol
    let mut result = zeros(n);
    let mut i = n;
    while i > 0 {
        i -= 1;
        let mut sum = 0.0;
        for j in i+1..n {
            sum += M[i * n + j] * result[j];
        }
        result[i] = (pol[i] - sum) / M[i * n + i];
    }

    result
}
// </vc-code>

}
fn main() {}