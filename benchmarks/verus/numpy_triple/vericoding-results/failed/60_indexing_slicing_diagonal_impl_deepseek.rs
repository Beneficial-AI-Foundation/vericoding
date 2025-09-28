// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed min function to return i32 and added decreases clause to diagonal */
fn min(a: i32, b: i32) -> i32 {
    if a < b { a } else { b }
}
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
/* code modified by LLM (iteration 5): Added decreases clause to while loops */
{
    let mut result = Vec::new();
    let n = a.len() as i32;
    let m = a[0].len() as i32;
    
    if offset >= 0 {
        let len = min(n, m - offset);
        
        let mut i: i32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                result@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[j as int][(j + offset) as int],
            decreases len - i
        {
            result.push(a[i as usize][(i + offset) as usize]);
            i += 1;
        }
    } else {
        let offset_abs = -offset;
        let len = min(n - offset_abs, m);
        
        let mut i: i32 = 0;
        while i < len
            invariant
                0 <= i <= len,
                result@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[(j + offset_abs) as int][j as int],
            decreases len - i
        {
            result.push(a[(i + offset_abs) as usize][i as usize]);
            i += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}