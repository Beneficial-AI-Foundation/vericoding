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
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by removing 'as int' casts and using usize calculations with checked_add for negative offset length */
    let n = a.len();
    let m = a[0].len();
    if offset >= 0 {
        let off = offset as usize;
        let diag_len = if n <= m - off {
            n
        } else {
            m - off
        };
        let mut result = Vec::with_capacity(diag_len);
        for i in 0..diag_len {
            result.push(a[i][i + off]);
        }
        result
    } else {
        let neg_off = (-offset) as usize;
        let diag_len = match n.checked_add(neg_off) {
            Some(newlen) if newlen <= m => newlen,
            _ => m,
        };
        let mut result = Vec::with_capacity(diag_len);
        for i in 0..diag_len {
            result.push(a[i + neg_off][i]);
        }
        result
    }
}
// </vc-code>

}
fn main() {}