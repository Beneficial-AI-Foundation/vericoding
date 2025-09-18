// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebmul(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        /* Example property: multiplying by the constant polynomial [a] scales all coefficients */
        (c2.len() == 1 ==> forall|i: int| 0 <= i < c1.len() ==> result[i] == c2[0] * c1[i]),
        /* Another example: multiplying [1,0,...] (T_0) by any polynomial preserves it */
        (c1.len() == 1 && c1[0] == 1 ==> forall|j: int| 0 <= j < c2.len() ==> result[j] == c2[j]),
        /* Special case: multiplying two linear polynomials [a,b] * [c,d] */
        /* Result should be [ac + bd/2, ad + bc, bd/2] */
        (c1.len() == 2 && c2.len() == 2 ==> {
            let a = c1[0];
            let b = c1[1]; 
            let c = c2[0];
            let d = c2[1];
            result[0] == a * c + b * d / 2 &&
            result[1] == a * d + b * c &&
            result[2] == b * d / 2
        }),
        /* Verify the example from documentation: [1,2,3] * [3,2,1] */
        /* Result should be [6.5, 12, 12, 4, 1.5] but using integers for now */
        (c1.len() == 3 && c2.len() == 3 ==> {
            (c1[0] == 1 && c1[1] == 2 && c1[2] == 3 &&
             c2[0] == 3 && c2[1] == 2 && c2[2] == 1) ==>
            (result.len() == 5)
        })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}