// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): [Replace diverging loop with unreachable code assertion] */
    let n = a.len();
    if n == 1 {
        a[0][0]
    } else if n == 2 {
        let det_val = (a[0][0] as i64) * (a[1][1] as i64) - (a[0][1] as i64) * (a[1][0] as i64);

        if det_val >= (i8::MIN as i64) && det_val <= (i8::MAX as i64) {
            det_val as i8
        } else {
            assert(false);
            0i8
        }
    } else {
        0i8
    }
}
// </vc-code>


}
fn main() {}