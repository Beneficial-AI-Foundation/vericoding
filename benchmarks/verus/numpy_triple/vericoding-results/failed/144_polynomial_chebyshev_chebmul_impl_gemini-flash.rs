// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Helper function for abs in Verus */
fn abs_i32(val: i32) -> i32 {
    if val < 0 {
        -val
    } else {
        val
    }
}
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
/* code modified by LLM (iteration 5): Added `decreases` clause to the while loop. */
{
    let l1 = c1.len();
    let l2 = c2.len();
    let mut result: Vec<i8> = Vec::new();
    let result_len: usize = l1 + l2 - 1;

    let mut k_init: usize = 0;
    while k_init < result_len
        invariant
            k_init <= result_len,
            result.len() == k_init,
        decreases result_len - k_init
    {
        result.push(0i8);
        k_init = k_init + 1;
    }

    if l1 == 0 || l2 == 0 {
        return result;
    }

    for i in 0..l1 {
        for j in 0..l2 {
            let k = i + j;
            let c1_i = c1[i];
            let c2_j = c2[j];

            // Term for T_{i+j}
            if k < result.len() {
                result.set(k, (result[k] as i32 + (c1_i as i32 * c2_j as i32) / 2) as i8);
            }

            // Term for T_{|i-j|}
            let i_int = i as i32;
            let j_int = j as i32;
            let k_abs_val = abs_i32(i_int - j_int);
            if k_abs_val < result.len() as i32 {
                // Special case for T_0 term (when i=j)
                if i == j {
                    result.set(k_abs_val as usize, (result[k_abs_val as usize] as i32 + c1_i as i32 * c2_j as i32) as i8);
                } else {
                    result.set(k_abs_val as usize, (result[k_abs_val as usize] as i32 + (c1_i as i32 * c2_j as i32) / 2) as i8);
                }
            }
        }
    }

    result
}
// </vc-code>


}
fn main() {}