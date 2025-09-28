// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix old() function usage with proper mutable reference syntax */
fn cheb_mul_term(input: Vec<i8>, coeff: i8, shift: usize, result: &mut Vec<i8>)
    requires
        input.len() > 0,
        result.len() == input.len() + shift,
        forall|i: int| 0 <= i < result.len() ==> result[i] as i64 >= -128 && result[i] as i64 <= 127,
        forall|i: int| 0 <= i < input.len() ==> input[i] as i64 >= -128 && input[i] as i64 <= 127,
    ensures
        result@.subrange(0, shift as int) == old(result)@.subrange(0, shift as int),
        forall|i: int| shift as int <= i < (shift + input.len()) as int ==> 
            result[i] as i64 == old(result@[i] as i64) + coeff as i64 * input[i - shift as int] as i64,
        result@.subrange((shift + input.len()) as int, result.len() as int) == old(result)@.subrange((shift + input.len()) as int, result.len() as int),
{
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result.len() == input.len() + shift,
            forall|k: int| 0 <= k < shift as int ==> result@[k] == old(result)@[k],
            forall|k: int| shift as int <= k < (shift + i) as int ==> 
                result[k] as i64 == old(result@[k] as i64) + coeff as i64 * input[k - shift as int] as i64,
            forall|k: int| (shift + i) as int <= k < result.len() as int ==> result@[k] == old(result)@[k],
        decreases input.len() - i,
    {
        let idx = shift + i;
        result[idx] = (result[idx] as i64 + coeff as i64 * input[i] as i64) as i8;
        i += 1;
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
/* code modified by LLM (iteration 5): Fix main implementation logic and ensure proper initialization */
{
    let n = c1.len();
    let m = c2.len();
    let mut result = Vec::new();
    result.resize(n + m - 1, 0i8);
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == n + m - 1,
    {
        cheb_mul_term(c2, c1[i], i, &mut result);
        if i > 0 {
            cheb_mul_term(c2, c1[i], i, &mut result);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}