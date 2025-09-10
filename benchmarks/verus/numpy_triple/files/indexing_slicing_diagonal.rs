/* Extract diagonal elements from a 2D matrix with optional offset.

Takes a 2D matrix and returns a 1D vector containing the diagonal elements.
For offset=0, returns main diagonal elements [a[0,0], a[1,1], ...].
For offset>0, returns elements above main diagonal [a[0,offset], a[1,offset+1], ...].
For offset<0, returns elements below main diagonal [a[-offset,0], a[-offset+1,1], ...]. */

use vstd::prelude::*;

verus! {
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
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}

fn main() {}