// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive Hermite basis for i32 with decreases */
fn hermite_basis_i32(k: usize, t: i32) -> i32 decreases k {
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis_i32(k - 1, t) - ((k - 1) as i32) * hermite_basis_i32(k - 2, t)
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
    /* code modified by LLM (iteration 5): build 2D Hermite Vandermonde safely with loop invariants */
    let n = x.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let cols = (x_deg + 1) * (y_deg + 1);
    let mut pi: usize = 0;
    while pi < n
        invariant pi <= n;
        invariant result.len() == pi;
        decreases n - pi;
    {
        let mut row: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i <= x_deg
            invariant i <= x_deg + 1;
            invariant row.len() <= cols;
            decreases (x_deg + 1) - i;
        {
            let hx = hermite_basis_i32(i, x[pi]);
            let mut j: usize = 0;
            while j <= y_deg
                invariant j <= y_deg + 1;
                invariant row.len() <= cols;
                decreases (y_deg + 1) - j;
            {
                let hy = hermite_basis_i32(j, y[pi]);
                row.push(hx * hy);
                j += 1;
            }
            i += 1;
        }
        proof {
            assert(row.len() == cols);
        }
        result.push(row);
        pi += 1;
    }
    result
}
// </vc-code>

}
fn main() {}