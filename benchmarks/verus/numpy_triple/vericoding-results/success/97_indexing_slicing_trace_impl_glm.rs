// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed overflow in negation and casting issues */
fn safe_add(a: usize, b: i32) -> Option<usize> {
    if b >= 0 {
        let b_usize = b as usize;
        if a <= usize::MAX - b_usize {
            Some(a + b_usize)
        } else {
            None
        }
    } else {
        if b == i32::MIN {
            None
        } else {
            let b_abs = -b;
            let b_abs_usize = b_abs as usize;
            if a >= b_abs_usize {
                Some(a - b_abs_usize)
            } else {
                None
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn trace(a: Vec<Vec<f32>>, offset: i32) -> (result: f32)
    ensures true
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added missing braces for method body */
{
    let mut sum = 0.0;
    let row_count = a.len();
    let mut i = 0;
    while i < row_count
        invariant
            i <= row_count,
            a.len() == row_count,
        decreases row_count - i
    {
        let row = &a[i];
        if let Some(col_index) = safe_add(i, offset) {
            if col_index < row.len() {
                sum += row[col_index];
            }
        }
        i += 1;
    }
    sum
}
// </vc-code>


}
fn main() {}