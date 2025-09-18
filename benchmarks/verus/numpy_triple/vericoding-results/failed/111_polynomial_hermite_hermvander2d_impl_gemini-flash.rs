// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn hermite_polynomial(n: nat, t: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        2 * t * hermite_polynomial((n - 1) as nat, t) - 2 * (n - 1) * hermite_polynomial((n - 2) as nat, t)
    }
}

fn hermvander2d(x: Vec<i32>, y: Vec<i32>, xdeg: usize, ydeg: usize) -> (result: Vec<Vec<i32>>)
    requires x.len() == y.len(),
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (xdeg + 1) * (ydeg + 1),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k][0] == 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed indexing by using `Vec::new().push()` and unwrapping the `Option` from `get_mut`. Corrected ghost variable usage and casting. Moved `x_val` and `y_val` from Vecs to `i32` before using in ghost context. */
{
    let n_points = x.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    if n_points == 0 {
        return result;
    }

    for i in 0..n_points {
        result.push(Vec::new());
        let x_val_i32: i32 = x[i];
        let y_val_i32: i32 = y[i];

        for dx_idx in 0..xdeg + 1 {
            for dy_idx in 0..ydeg + 1 {
                let h_x = hermite_polynomial(dx_idx as nat, x_val_i32 as int);
                let h_y = hermite_polynomial(dy_idx as nat, y_val_i32 as int);
                
                let val = (h_x * h_y) as i32;
                result.get_mut(i).unwrap().push(val);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}