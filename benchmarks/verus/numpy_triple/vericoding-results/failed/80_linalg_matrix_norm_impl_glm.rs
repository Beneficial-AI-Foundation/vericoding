// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fix type mismatch in abs_val_i8 */
fn abs_val_i8(x: i8) -> (abs: i8)
    ensures
        abs >= 0,
        abs == if x >= 0 { x } else { -x as i8 },
{
    if x >= 0 {
        x
    } else {
        -x as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn matrix_norm(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result as int >= 0,
        (result as int == 0) == (forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> #[trigger] x@[i][j] == 0),
        forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> abs_val(#[trigger] x@[i][j] as int) <= result as int,
        (exists|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() && #[trigger] x@[i][j] != 0) ==> result as int > 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix type mismatches in loop invariants by converting loop variables to int */
{
    let mut max_abs = 0i8;
    let n = x.len();
    for i in 0..n
        invariant 
            0 <= i <= n,
            max_abs >= 0,
            forall|k: int, l: int| 
                0 <= k < (i as int) && 0 <= l < x@[k].len() ==> abs_val(x@[k][l] as int) <= max_abs as int,
        decreases n - i
    {
        let row = x[i];
        let row_len = row.len();
        for j in 0..row_len
            invariant
                0 <= j <= row_len,
                max_abs >= 0,
                forall|k: int, l: int| 
                    0 <= k < (i as int) && 0 <= l < x@[k].len() ==> abs_val(x@[k][l] as int) <= max_abs as int,
                forall|l: int| 
                    0 <= l < (j as int) ==> abs_val(x@[i][l] as int) <= max_abs as int,
            decreases row_len - j
        {
            let val = row[j];
            let abs_val_val = abs_val_i8(val);
            if abs_val_val > max_abs {
                max_abs = abs_val_val;
            }
        }
    }
    max_abs
}
// </vc-code>


}
fn main() {}