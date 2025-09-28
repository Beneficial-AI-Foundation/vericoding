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
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    let n = c1.len();
    let m = c2.len();
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < n + m - 1
        invariant
            0 <= i <= n + m - 1,
            result.len() == i,
        decreases n + m - 1 - i
    {
        let mut coeff: i32 = 0;
        
        let mut j = 0;
        while j <= i
            invariant
                0 <= j <= i + 1,
            decreases i + 1 - j
        {
            if j < n && i - j < m {
                let c1_val = c1[j] as i32;
                let c2_val = c2[i - j] as i32;
                
                if j == 0 || i - j == 0 {
                    coeff = coeff + c1_val * c2_val;
                } else {
                    coeff = coeff + c1_val * c2_val / 2;
                }
                
                if j > 0 && i + j < n + m - 1 && i + j - j < m {
                    if i + j < n {
                        let c1_val2 = c1[i + j] as i32;
                        let c2_val2 = c2[0] as i32;
                        coeff = coeff + c1_val2 * c2_val2 / 2;
                    } else if j < n && i + j - j < m {
                        let c1_val2 = c1[j] as i32;
                        let c2_val2 = c2[i + j - j] as i32;
                        coeff = coeff + c1_val2 * c2_val2 / 2;
                    }
                }
            }
            j = j + 1;
        }
        
        result.push(coeff as i8);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}