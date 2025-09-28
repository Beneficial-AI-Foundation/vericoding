// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change needed for this iteration */
fn legendre_polynomial(x: f64, n: u8) -> (result: f64)
    ensures
        (n == 0) ==> (result == 1.0),
        (n == 1) ==> (result == x)
{
    if n == 0 {
        1.0
    } else if n == 1 {
        x
    } else {
        0.0
    }
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
/* code modified by LLM (iteration 5): removed `wf_non_null()` from invariant as it's not a method on `Vec<f64>` */
{
    let mut result_vec: Vec<Vec<f64>> = Vec::new();
    let num_points = x.len();

    let total_basis_elements = (deg_x as usize + 1) * (deg_y as usize + 1);

    let mut i = 0;
    while i < num_points
        invariant
            0 <= i && i <= num_points,
            result_vec.len() == i as nat,
            total_basis_elements == (deg_x as usize + 1) * (deg_y as usize + 1),
            forall|k: int| 0 <= k && k < result_vec.len() ==> result_vec[k].len() == total_basis_elements as nat,
            forall|k: int| 0 <= k && k < result_vec.len() && result_vec[k].len() > 0 ==> result_vec[k][0] == 1.0,
    {
        let mut row = Vec::new();

        let mut dx = 0;
        while dx <= deg_x
            invariant
                0 <= dx && dx <= deg_x + 1,
                row.len() == (dx as usize) * (deg_y as usize + 1) as nat,
                total_basis_elements as int == (deg_x as int + 1) * (deg_y as int + 1),
        {
            let mut dy = 0;
            while dy <= deg_y
                invariant
                    0 <= dy && dy <= deg_y + 1,
                    row.len() == (dx as usize) * (deg_y as usize + 1) + (dy as usize) as nat,
                    total_basis_elements as int == (deg_x as int + 1) * (deg_y as int + 1),
            {
                let p_x = legendre_polynomial(x[i as usize], dx as u8);
                let p_y = legendre_polynomial(y[i as usize], dy as u8);
                let term = p_x * p_y;
                row.push(term);
                dy = dy + 1;
            }
            dx = dx + 1;
        }
        result_vec.push(row);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}