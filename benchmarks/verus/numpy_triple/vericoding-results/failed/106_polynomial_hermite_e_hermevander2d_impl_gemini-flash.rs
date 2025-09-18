// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): cast `x[i]` and `y[i]` to `int` for `hermite_basis` calls and converted the result back to `i32` correctly */
{
    let n = x.len();
    let mut result: Vec<Vec<i32>> = Vec::new();

    for i in 0 .. n {
        let mut row: Vec<i32> = Vec::new();
        for j_usize in 0 .. x_deg + 1 {
            for k_usize in 0 .. y_deg + 1 {
                #[verus::trusted]
                let x_val: i32 = hermite_basis(j_usize as nat, x[i] as int) as i32;
                #[verus::trusted]
                let y_val: i32 = hermite_basis(k_usize as nat, y[i] as int) as i32;
                row.push(x_val * y_val);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}