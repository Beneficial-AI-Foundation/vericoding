// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper function for computing Hermite polynomials */
fn hermite_poly(n: usize, x: f64) -> f64
    decreases n
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        let n_minus_1 = n - 1;
        let coeff = n_minus_1 as f64;
        x * hermite_poly(n_minus_1, x) - coeff * hermite_poly(n - 2, x)
    }
}
// </vc-helpers>

// <vc-spec>
fn hermevander(x: Vec<f64>, deg: usize) -> (result: Vec<Vec<f64>>)
    requires deg >= 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == deg + 1,
        forall|i: int| 0 <= i < result.len() ==> result[i][0] == 1.0,
        deg > 0 ==> forall|i: int| 0 <= i < result.len() ==> result[i][1] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting for usize indices */
    let mut result: Vec<Vec<f64>> = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int].len() == deg + 1,
            forall|j: int| 0 <= j < i ==> result[j as int][0] == 1.0,
            deg > 0 ==> forall|j: int| 0 <= j < i ==> result[j as int][1] == x[j],
    {
        let mut row: Vec<f64> = Vec::new();
        for k in 0..(deg + 1)
            invariant
                row.len() == k,
                k > 0 ==> row[0] == 1.0,
                deg > 0 && k > 1 ==> row[1] == x[i],
        {
            if k == 0 {
                row.push(1.0);
            } else if k == 1 {
                row.push(x[i]);
            } else {
                let prev_val = row[(k - 1) as usize];
                let prev_prev_val = row[(k - 2) as usize];
                let coeff = (k - 1) as f64;
                let new_val = x[i] * prev_val - coeff * prev_prev_val;
                row.push(new_val);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}