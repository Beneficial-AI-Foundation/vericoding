// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): generate Chebyshev monomial coefficients */
fn chebyshev_monomial_coeffs(n: usize) -> Vec<Vec<f64>> {
    let mut T: Vec<Vec<f64>> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        decreases n - k;
        let mut coeffs: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            decreases n - j;
            coeffs.push(0.0);
            j += 1;
        }
        if k == 0 {
            coeffs[0] = 1.0;
        } else if k == 1 {
            coeffs[1] = 1.0;
        } else {
            let mut j: usize = 0;
            while j < n {
                decreases n - j;
                let term1 = if j >= 1 { 2.0 * T[k - 1][j - 1] } else { 0.0 };
                let term2 = T[k - 2][j];
                coeffs[j] = term1 - term2;
                j += 1;
            }
        }
        T.push(coeffs);
        k += 1;
    }
    T
}
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
    /* code modified by LLM (iteration 5): add decreases clauses to loops for verification */
    let n: usize = pol.len();
    let cheb = chebyshev_monomial_coeffs(n);
    let mut a: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        decreases n - i;
        a.push(pol[i]);
        i += 1;
    }
    let mut result: Vec<f64> = Vec::new();
    let mut _k: usize = 0;
    while _k < n {
        decreases n - _k;
        result.push(0.0);
        _k += 1;
    }
    let mut idx: usize = 0;
    while idx < n {
        decreases n - idx;
        let m = n - 1 - idx;
        let leading = if m == 0 { 1.0 } else {
            let mut pow: f64 = 1.0;
            let mut t: usize = 0;
            while t < (m - 1) {
                decreases (m - 1) - t;
                pow = pow * 2.0;
                t += 1;
            }
            pow
        };
        let c = a[m] / leading;
        result[m] = c;
        let mut j: usize = 0;
        while j < (m + 1) {
            decreases (m + 1) - j;
            a[j] = a[j] - c * cheb[m][j];
            j += 1;
        }
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}