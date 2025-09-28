// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed max_i from int to usize and declared i as usize to allow these variables in executable code, fixing compilation error */
fn compute_legendre(x: f64, max_deg: u8) -> (result: Vec<f64>)
    ensures
        result.len() == max_deg as int + 1,
        0 <= max_deg as int ==> result[0] == 1.0,
{
    let max_i = max_deg as usize;
    let mut res = Vec::new();
    if max_deg >= 0 {
        res.push(1.0);
    }
    if max_deg >= 1 {
        res.push(x);
    }
    let mut i: usize = 2;
    while i <= max_i
        invariant
            res.len() as int == i as int,
        decreases max_i as int - i as int,
    {
        let n = i as f64;
        let prev1 = res[i - 1];
        let prev2 = res[i - 2];
        let new_val = ((2.0 * n - 1.0) * x * prev1 - (n - 1.0) * prev2) / n;
        res.push(new_val);
        i += 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn legvander2d(x: Vec<f64>, y: Vec<f64>, deg_x: u8, deg_y: u8) -> (result: Vec<Vec<f64>>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == (deg_x as int + 1) * (deg_y as int + 1),
        forall|i: int| 0 <= i < result.len() && result[i].len() > 0 ==> result[i][0] == 1.0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implementation of legvander2d using nested loops */
{
    let mut result = Vec::new();
    let num_points = x.len();
    let mut i = 0usize;
    while i < num_points
        invariant
            result.len() == i,
        decreases (num_points as int - i as int),
    {
        let rx = x[i];
        let ry = y[i];
        let leg_x = compute_legendre(rx, deg_x);
        let leg_y = compute_legendre(ry, deg_y);
        let mut vec_inner = Vec::new();
        let mut m = 0u8;
        while m <= deg_x
            invariant
                vec_inner.len() as int == (m as usize as int) * ((deg_y as usize as int) + 1),
            decreases (deg_x as int - m as int),
        {
            let pm = leg_x[m as usize];
            let mut n = 0u8;
            while n <= deg_y
                invariant
                    vec_inner.len() as int == (m as usize as int) * ((deg_y as usize as int) + 1) + (n as usize as int),
                decreases (deg_y as int - n as int),
            {
                vec_inner.push(pm * leg_y[n as usize]);
                n += 1;
            }
            m += 1;
        }
        result.push(vec_inner);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}