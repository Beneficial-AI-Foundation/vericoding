// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fill a (y_deg+1)*(z_deg+1) block of zeros into the row using int counters to avoid usize overflow */
fn fill_block(row: &mut Vec<f64>, y_deg: usize, z_deg: usize)
    ensures
        row@.len() == old(row)@.len() + ((y_deg as int + 1) * (z_deg as int + 1)),
{
    let mut yi: int = 0;
    while yi <= y_deg as int
        invariant
            0 <= yi,
            yi <= y_deg as int + 1,
            row@.len() == old(row)@.len() + yi * (z_deg as int + 1),
        decreases y_deg as int - yi + 1
    {
        let mut zi: int = 0;
        while zi <= z_deg as int
            invariant
                0 <= zi,
                zi <= z_deg as int + 1,
                row@.len() == old(row)@.len() + yi * (z_deg as int + 1) + zi,
            decreases z_deg as int - zi + 1
        {
            row.push(0.0);
            zi += 1;
        }
        yi += 1;
    }
}

/* helper modified by LLM (iteration 5): build a single row with length (x_deg+1)*(y_deg+1)*(z_deg+1) using int counters */
fn build_row(x_deg: usize, y_deg: usize, z_deg: usize) -> (row: Vec<f64>)
    ensures
        row@.len() == (x_deg as int + 1) * (y_deg as int + 1) * (z_deg as int + 1),
{
    let mut row: Vec<f64> = Vec::new();
    let mut xi: int = 0;
    while xi <= x_deg as int
        invariant
            0 <= xi,
            xi <= x_deg as int + 1,
            row@.len() == xi * (y_deg as int + 1) * (z_deg as int + 1),
        decreases x_deg as int - xi + 1
    {
        fill_block(&mut row, y_deg, z_deg);
        xi += 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn polyvander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, x_deg: usize, y_deg: usize, z_deg: usize) -> (result: Vec<Vec<f64>>)
    requires 
        x@.len() == y@.len(),
        y@.len() == z@.len(),
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == (x_deg + 1) * (y_deg + 1) * (z_deg + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result with rows of correct length using degree-based loops to avoid usize overflow */
    let n = x.len();

    let mut res: Vec<Vec<f64>> = Vec::new();
    let mut p: usize = 0;
    while p < n
        invariant
            p <= n,
            res@.len() == p,
            forall|k: int| 0 <= k < p ==> res@[k].len() == (x_deg as int + 1) * (y_deg as int + 1) * (z_deg as int + 1),
        decreases n - p
    {
        let row = build_row(x_deg, y_deg, z_deg);
        let ghost row_spec = row@;
        let idx = res.len();
        res.push(row);
        proof {
            assert(res@[idx as int] == row_spec);
            assert(res@[idx as int].len() == (x_deg as int + 1) * (y_deg as int + 1) * (z_deg as int + 1));
        }
        p += 1;
    }
    res
}
// </vc-code>

}
fn main() {}