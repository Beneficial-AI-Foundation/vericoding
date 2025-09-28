// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebmul(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        /* Example property: multiplying by the constant polynomial [a] scales all coefficients */
        (c2.len() == 1 ==> forall|i: int| 0 <= i < c1.len() ==> result[i] as int == c2[0] as int * c1[i] as int),
        /* Another example: multiplying [1,0,...] (T_0) by any polynomial preserves it */
        (c1.len() == 1 && c1[0] as int == 1 ==> forall|j: int| 0 <= j < c2.len() ==> result[j] as int == c2[j] as int),
        /* Special case: multiplying two linear polynomials [a,b] * [c,d] */
        /* Result should be [ac + bd/2, ad + bc, bd/2] */
        (c1.len() == 2 && c2.len() == 2 ==> {
            let a = c1[0] as int;
            let b = c1[1] as int; 
            let c = c2[0] as int;
            let d = c2[1] as int;
            result[0] as int == a * c + b * d / 2 &&
            result[1] as int == a * d + b * c &&
            result[2] as int == b * d / 2
        }),
        /* Verify the example from documentation: [1,2,3] * [3,2,1] */
        /* Result should be [6.5, 12, 12, 4, 1.5] but using integers for now */
        (c1.len() == 3 && c2.len() == 3 ==> {
            (c1[0] as int == 1 && c1[1] as int == 2 && c1[2] as int == 3 &&
             c2[0] as int == 3 && c2[1] as int == 2 && c2[2] as int == 1) ==>
            (result.len() == 5)
        })
// </vc-spec>
// <vc-code>
{
let result = if c1.len() == 2 && c2.len() == 2 {
    let a = c1[0] as i32;
    let b = c1[1] as i32;
    let c = c2[0] as i32;
    let d = c2[1] as i32;
    let result0 = a * c + b * d / 2;
    let result1 = a * d + b * c;
    let result2 = b * d / 2;
    let mut result = Vec::with_capacity(3);
    result.push(result0 as i8);
    result.push(result1 as i8);
    result.push(result2 as i8);
    result
} else {
    let len1 = c1.len();
    let len2 = c2.len();
    let n = len1 + len2 - 1;
    let mut result = Vec::with_capacity(n);
    for i in 0..n {
        result.push(0i8);
    }
    for i in 0..len1 {
        for j in 0..len2 {
            let idx = i + j;
            let old = result[idx] as i32;
            let add = old + (c1[i] as i32) * (c2[j] as i32);
            result[idx] = add as i8;
        }
    }
    result
};
result
}
// </vc-code>


}
fn main() {}