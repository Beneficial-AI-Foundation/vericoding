// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed ghost cast from index access */
spec fn get_coefficient(pol: &Seq<f64>, i: usize, j: usize) -> f64
{
    if i == 0 {
        return pol.index(j);
    }
    if i == 1 {
        if j == 0 { return 0.0; }
        return pol.index(j - 1) / 2.0;
    }
    if j < i {
        return 0.0;
    }
    if j == i {
        return pol.index(0) / (2.0f64.powi(i as i32));
    }
    pol.index(j - 1) / 2.0 + pol.index(j + 1) / 2.0
}

proof fn powi_distributes(a: f64, b: f64, i: int)
    requires i >= 0
    ensures (a * b).powi(i as i32) == a.powi(i as i32) * b.powi(i as i32)
{
}

proof fn powi_pos_base(a: f64, i: int)
    requires a > 0.0, i >= 0
    ensures a.powi(i as i32) > 0.0
{
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
/* code modified by LLM (iteration 5): Cast `i as int` to `i as isize` in loop condition */
{
    let n: usize = pol.len();

    if n == 0 {
        return Vec::new();
    }

    let mut c: Vec<f64> = Vec::with_capacity(n);
    for _ in 0..n {
        c.push(0.0);
    }

    if n == 1 {
        return Vec::from(vec![pol[0]]);
    }

    // Populate c based on logic similar to numpy's poly2cheb
    let mut new_c_vec: Vec<f64> = Vec::with_capacity(n);
    for _ in 0..n { new_c_vec.push(0.0); }

    new_c_vec[n - 1] = pol[n - 1];
    if n >= 2 {
        new_c_vec[n - 2] = pol[n - 2] + pol[n - 1] * 2.0;
    }

    let mut i = n - 3;
    while (i as isize) >= 0
        invariant
            n == pol.len(),
            new_c_vec.len() == n,
            i < n - 2,
            i >= 0 || n < 3, // Changed invariant to handle i moving to -1
    {
        new_c_vec[i] = pol[i] + new_c_vec[i + 1] * 2.0 - new_c_vec[i + 2];
        if i == 0 { break; }
        i = i - 1;
    }
    
    // Normalize to get the Chebyshev coefficients
    let mut result: Vec<f64> = Vec::with_capacity(n);
    for _ in 0..n {
        result.push(0.0);
    }

    if n > 0 {
        result[0] = new_c_vec[0] / 2.0;
    }
    if n > 1 {
        result[1] = new_c_vec[1] / 2.0;
    }

    for k in 2..n {
        result[k] = new_c_vec[k] / 2.0;
    }

    result
}
// </vc-code>

}
fn main() {}