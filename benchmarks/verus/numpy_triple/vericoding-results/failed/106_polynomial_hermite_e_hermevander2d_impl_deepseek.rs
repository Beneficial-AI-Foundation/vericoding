// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add decreases clause to iterative function */
fn hermite_basis_iterative(k: usize, t: i32) -> i32 
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let prev1 = hermite_basis_iterative(k - 1, t);
        let prev2 = hermite_basis_iterative(k - 2, t);
        t.wrapping_mul(prev1).wrapping_sub((k - 1) as i32 * prev2)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(k: nat, t: int) -> int
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t)
    }
}

fn hermevander2d(x: Vec<i32>, y: Vec<i32>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<i32>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|point_idx: int| 0 <= point_idx < result.len() ==> 
            result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add decreases clause to while loop */
{
    let num_points = x.len();
    let num_coeffs = (x_deg + 1) * (y_deg + 1);
    let mut result_vec: Vec<Vec<i32>> = Vec::with_capacity(num_points);
    let mut i: usize = 0;
    while i < num_points 
        decreases num_points - i
    {
        let mut row: Vec<i32> = Vec::with_capacity(num_coeffs);
        let mut kx: usize = 0;
        while kx <= x_deg 
            decreases x_deg + 1 - kx
        {
            let mut ky: usize = 0;
            while ky <= y_deg 
                decreases y_deg + 1 - ky
            {
                let x_val = x[i];
                let y_val = y[i];
                let basis_x = hermite_basis_iterative(kx, x_val);
                let basis_y = hermite_basis_iterative(ky, y_val);
                let value = basis_x.wrapping_mul(basis_y);
                row.push(value);
                ky += 1;
            }
            kx += 1;
        }
        result_vec.push(row);
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}