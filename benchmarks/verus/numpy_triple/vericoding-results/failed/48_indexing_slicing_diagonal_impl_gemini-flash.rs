// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a.len() > 0,
        a.len() > 0 ==> a[0].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len(),
        if offset >= 0 { 
            offset as int <= a[0].len() as int
        } else { 
            (-offset) as int <= a.len() as int
        },
    ensures
        result.len() == (if offset >= 0 { 
            if a.len() as int <= (a[0].len() as int - offset as int) { a.len() as int } else { a[0].len() as int - offset as int }
        } else { 
            if (a.len() as int + (-offset) as int) <= a[0].len() as int { a.len() as int + (-offset) as int } else { a[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result.len() ==> {
            if offset >= 0 {
                #[trigger] result[i] == a[i][i + offset as int]
            } else {
                #[trigger] result[i] == a[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed indexing logic and added `proof` blocks for loop invariants. */
{
    let rows = a.len();
    let cols = a[0].len();
    let mut result = Vec::new();

    if offset >= 0 {
        let offset_val = offset as usize;
        let mut i: usize = 0;
        let effective_cols = if cols >= offset_val { cols - offset_val } else { 0 };
        let len_val = if rows <= effective_cols { rows } else { effective_cols };

        while i < len_val
            invariant
                0 <= i,
                i <= len_val,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result[j as usize] == a[j as usize][j as usize + offset_val],
            decreases len_val - i
        {
            proof {
                assert(i < rows);
                assert(i + offset_val < cols);
            }
            result.push(a[i][i + offset_val]);
            i = i + 1;
        };
    } else {
        let neg_offset_val = (-offset) as usize;
        let mut i: usize = 0;
        let effective_rows = if rows >= neg_offset_val { rows - neg_offset_val } else { 0 };
        let len_val = if effective_rows <= cols { effective_rows } else { cols };
        
        while i < len_val
            invariant
                0 <= i,
                i <= len_val,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result[j as usize] == a[j as usize + neg_offset_val][j as usize],
            decreases len_val - i
        {
            proof {
                assert(i + neg_offset_val < rows);
                assert(i < cols);
            }
            result.push(a[i + neg_offset_val][i]);
            i = i + 1;
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}