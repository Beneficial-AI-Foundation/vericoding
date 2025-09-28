// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section was empty, added a placeholder to satisfy the expected format. */

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
/* code modified by LLM (iteration 5): The previous change caused a compilation error. Fixing the compilation error in the nested while loop's invariant by separating conditions with commas. */
{
    let rows = x.len();
    let cols = x@[0].len();
    let mut max_abs_val: i8 = 0;
    let mut i: usize = 0;

    while i < rows
        invariant
            0 <= i as int <= rows as int,
            forall|row_idx: int, col_idx: int|
                0 <= row_idx < i as int && 0 <= col_idx < cols as int
                ==>
                abs_val(x@[row_idx]@[col_idx] as int) <= max_abs_val as int,
            max_abs_val as int >= 0,
        decreases rows - i
    {
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= i as int && i as int < rows as int,
                0 <= j as int <= cols as int,
                forall|col_idx: int|
                    0 <= col_idx < j as int
                    ==>
                    abs_val(x@[i as int]@[col_idx] as int) <= max_abs_val as int,
                forall|row_idx: int, col_idx: int|
                    0 <= row_idx < i as int && 0 <= col_idx < cols as int
                    ==>
                    abs_val(x@[row_idx]@[col_idx] as int) <= max_abs_val as int,
                max_abs_val as int >= 0,
            decreases cols - j
        {
            let current_val = x@[i as int]@[j as int];
            let current_abs_val = abs_val(current_val as int);
            if current_abs_val > max_abs_val as int {
                max_abs_val = current_abs_val as i8;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    max_abs_val
}
// </vc-code>


}
fn main() {}