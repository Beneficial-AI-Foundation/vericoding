/* Extract diagonal elements from a 2D matrix with optional offset.
    
Takes a 2D matrix and returns a 1D vector containing the diagonal elements.
For offset=0, returns main diagonal elements [a[0,0], a[1,1], ...].
For offset>0, returns elements above main diagonal [a[0,offset], a[1,offset+1], ...].
For offset<0, returns elements below main diagonal [a[-offset,0], a[-offset+1,1], ...].

Specification: diagonal extracts diagonal elements from a 2D matrix.
    
Precondition: The matrix dimensions must be large enough to accommodate the offset
Postcondition: The result contains exactly the diagonal elements at the specified offset */

use vstd::prelude::*;

verus! {
fn diagonal(a: &Vec<Vec<i32>>, offset: int) -> (result: Vec<i32>)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len(),
        if offset >= 0 {
            offset <= a[0].len()
        } else {
            (-offset) <= a.len()
        },
    ensures
        result.len() == if offset >= 0 {
            if (a.len() as int) <= (a[0].len() as int) - offset {
                a.len()
            } else {
                (a[0].len() as int - offset) as usize
            }
        } else {
            if (a.len() as int) + offset <= (a[0].len() as int) {
                (a.len() as int + offset) as usize
            } else {
                a[0].len()
            }
        },
        forall|i: int| 0 <= i < result.len() ==> {
            if offset >= 0 {
                #[trigger] result[i] == a[i][i + offset]
            } else {
                #[trigger] result[i] == a[i + (-offset)][i]
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