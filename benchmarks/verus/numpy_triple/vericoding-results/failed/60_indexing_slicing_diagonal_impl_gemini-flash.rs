// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a@.len() > 0,
        a@.len() > 0 ==> a@[0].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> #[trigger] a@[i].len() == a@[0].len(),
        if offset >= 0 { 
            offset as int <= a@[0].len() as int
        } else { 
            (-offset) as int <= a@.len() as int
        },
    ensures
        result@.len() == (if offset >= 0 { 
            if a@.len() as int <= (a@[0].len() as int - offset as int) { a@.len() as int } else { a@[0].len() as int - offset as int }
        } else { 
            if (a@.len() as int + (-offset) as int) <= a@[0].len() as int { a@.len() as int + (-offset) as int } else { a@[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result@.len() ==> {
            if offset >= 0 {
                #[trigger] result@[i] == a@[i][i + offset as int]
            } else {
                #[trigger] result@[i] == a@[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected loop bounds and invariants for diagonal extraction, addressing integer overflow/underflow and out-of-bounds access. */
{
    let mut result = Vec::new();
    let num_rows = a.len();
    let num_cols = a[0].len();

    if offset >= 0 {
        let offset_usize = offset as usize;
        let mut i: usize = 0;
        let max_val_rows = (num_rows as int).min(num_cols as int - offset as int) as usize;

        while i < max_val_rows
            invariant
                0 <= i,
                i <= max_val_rows,
                i <= num_rows,
                (i + offset_usize) <= num_cols,
                result@.len() == i,
                forall|k: int| 0 <= k < i as int ==> 
                    (k as usize) < num_rows && (k as usize + offset_usize) < num_cols
                    && #[trigger] result@[k] == a@[k][k + offset as int],
            decreases max_val_rows - i
        {
            result.push(a[i][i + offset_usize]);
            i = i + 1;
        }
    } else {
        let neg_offset_usize = (-offset) as usize;
        let mut i: usize = 0;
        let max_val_cols = (num_cols as int).min(num_rows as int + offset as int) as usize;

        while i < max_val_cols
            invariant
                0 <= i,
                i <= max_val_cols,
                (i + neg_offset_usize) <= num_rows,
                i <= num_cols,
                result@.len() == i,
                forall|k: int| 0 <= k < i as int ==> 
                    (k as usize + neg_offset_usize) < num_rows && (k as usize) < num_cols
                    && #[trigger] result@[k] == a@[k + (-offset) as int][k],
            decreases max_val_cols - i
        {
            result.push(a[i + neg_offset_usize][i]);
            i = i + 1;
        }
    }

    return result;
}
// </vc-code>

}
fn main() {}