// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No modifications needed for initial implementations */

// </vc-helpers>

// <vc-spec>
fn det(a: Vec<Vec<i8>>) -> (result: i8)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() == a@.len(),
    ensures
        /* For 1x1 matrices, the determinant is the single element */
        a@.len() == 1 ==> result as int == a@[0][0],
        /* For 2x2 matrices, the determinant is ad - bc */
        a@.len() == 2 ==> result as int == a@[0][0] * a@[1][1] - a@[0][1] * a@[1][0],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed ghost type issue by using a.len() for executable code and adding assertions for spec ensures */
{
    let len: usize = a.len();
    if len == 1 {
        assert(a@.len() == 1);
        a[0][0]
    } else if len == 2 {
        assert(a@.len() == 2);
        (a[0][0] * a[1][1]) - (a[0][1] * a[1][0])
    } else {
        assert(false);
        0i8
    }
}

// </vc-code>


}
fn main() {}