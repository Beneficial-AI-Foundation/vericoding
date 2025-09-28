// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed all type mismatches and indexing issues with proper nat handling */
fn compute_cheb_coeffs(pol: &Vec<f64>, n: nat) -> (Vec<f64>, Vec<f64>)
    requires n == pol@.len()
{
    let mut a = Vec::new();
    let mut b = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant
            0 <= i <= n,
            a@.len() == i,
            b@.len() == i,
        decreases n - i
    {
        if i == 0 {
            a.push(0.0);
            b.push(pol@[n - 1]);
        } else {
            let a_prev = a@[i - 1];
            let b_prev = b@[i - 1];
            a.push(0.5 * b_prev);
            let next_val = if i < n - 1 { 
                pol@[n - 1 - i] + 0.5 * a_prev 
            } else { 
                0.5 * a_prev 
            };
            b.push(next_val);
        }
        i = i + 1;
    }
    (a, b)
}

fn reverse_coeffs(coeffs: Vec<f64>) -> Vec<f64> 
    requires coeffs@.len() > 0
{
    let n = coeffs@.len();
    let mut result = Vec::with_capacity(n as usize);
    let mut i: nat = n;
    while i > 0
        invariant
            0 <= i <= n,
            result@.len() == n - i,
        decreases i
    {
        i = i - 1;
        result.push(coeffs@[i]);
    }
    result
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
/* code modified by LLM (iteration 5): fixed type conversions and proper handling with proper nat casting */
{
    let n: nat = pol@.len();
    let (a_coeffs, b_coeffs) = compute_cheb_coeffs(&pol, n);
    let cheb_coeffs = if (n as int) % 2 == 0 {
        b_coeffs
    } else {
        a_coeffs
    };
    reverse_coeffs(cheb_coeffs)
}
// </vc-code>

}
fn main() {}