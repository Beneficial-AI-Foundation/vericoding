// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No functional changes. */
fn hermite_basis_exec(k: usize, t: i32) -> (res: i32)
    ensures res == hermite_basis(k as nat, t as int)
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        let h_k_minus_1 = hermite_basis_exec(k - 1, t);
        let h_k_minus_2 = hermite_basis_exec(k - 2, t);
        let term1 = t * h_k_minus_1;
        let term2 = (k - 1) as i32 * h_k_minus_2;
        term1 - term2
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
{
    /* code modified by LLM (iteration 3): Added decreases clauses to all while loops to prove termination. */
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            x.len() == y.len(),
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (x_deg + 1) * (y_deg + 1),
        decreases x.len() - i
    {
        let x_val = x[i];
        let y_val = y[i];

        let mut row: Vec<i32> = Vec::new();
        let mut y_d: usize = 0;
        while y_d <= y_deg
            invariant
                0 <= y_d <= y_deg + 1,
                row.len() == y_d * (x_deg + 1),
            decreases y_deg - y_d
        {
            let mut x_d: usize = 0;
            while x_d <= x_deg
                invariant
                    0 <= x_d <= x_deg + 1,
                    row.len() == y_d * (x_deg + 1) + x_d,
                decreases x_deg - x_d
            {
                let hx = hermite_basis_exec(x_d, x_val);
                let hy = hermite_basis_exec(y_d, y_val);
                row.push(hx * hy);
                x_d = x_d + 1;
            }
            y_d = y_d + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}