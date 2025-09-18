// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed. */
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
/* code modified by LLM (iteration 5): Corrected `to_vec()` issue by using `vstd::vec::Vec::from_seq`, fixed `pol[j as usize]` by casting `j` to `usize`, and addressed floating-point type casting in loop invariant. */
{
    let n = pol.len();
    if n == 0 {
        return Vec::new();
    }

    let mut result: Vec<f64> = Vec::new();
    result.resize(n, 0.0);
    let mut pol_s: vstd::vec::Vec<f64> = vstd::vec::Vec::from_seq(Seq::new(n as nat, |j: int| pol[j as usize]));

    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == n,
            pol_s.len() == n,
            i <= n,
    {
        // This loop applies the recurrence relation backward for the current polynomial coefficient
        // The coefficient of H_i is calculated from a_i * H_i + a_{i+1} * H_{i+1} + ...
        // The final result[i] will store the coefficient for H_i
        

        let mut j: usize = n - 1;
        while (j >= i)
            invariant
                result.len() == n,
                pol_s.len() == n,
                j >= i || (i == 0 && j == usize::MAX),
                j < n,
        {
            let current_coeff_val;
            if j == n - 1 {
                current_coeff_val = pol_s[j];
            } else {
                current_coeff_val = pol_s[j] + pol_s[j + 1] * 2.0 * ((j + 1) as f64);
            }
            pol_s.set(j, current_coeff_val);
            
            if j == 0 {
                break;
            }
            j = j - 1;
        }

        result.set(i, pol_s[i]);

        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}