// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }

/* helper modified by LLM (iteration 5): changed to use usize instead of int for executable code */
fn min_usize_exec(a: usize, b: usize) -> usize { if a < b { a } else { b } }
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
{
    /* code modified by LLM (iteration 5): added decreases clauses to while loops */
    let mut result: Vec<f64> = Vec::new();
    
    if offset >= 0 {
        let offset_pos = offset as usize;
        let max_len = min_usize_exec(a.len(), a[0].len() - offset_pos);
        
        let mut i = 0;
        while i < max_len
            invariant
                0 <= i <= max_len,
                max_len <= a.len(),
                max_len <= a[0].len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == a[j][j + offset as int],
            decreases max_len - i
        {
            result.push(a[i][i + offset_pos]);
            i += 1;
        }
    } else {
        let offset_neg = (-offset) as usize;
        let max_len = min_usize_exec(a.len() - offset_neg, a[0].len());
        
        let mut i = 0;
        while i < max_len
            invariant
                0 <= i <= max_len,
                max_len <= a.len(),
                max_len <= a[0].len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == a[j + (-offset) as int][j],
            decreases max_len - i
        {
            result.push(a[i + offset_neg][i]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}