// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to fix compilation error */
fn poly_coeff(c1: &Vec<i8>, c2: &Vec<i8>, k: usize) -> (result: i64)
    requires
        k < c1.len() + c2.len(),
{
    let mut sum = 0i64;
    let mut i = 0usize;
    while i <= k && i < c1.len()
        invariant
            0 <= i <= k + 1,
            i <= c1.len(),
        decreases k + 1 - i
    {
        let j = k - i;
        if j < c2.len() {
            sum = sum + (c1[i] as i64) * (c2[j] as i64);
        }
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] as int == c1[i] as int * c2[0] as int,
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] as int == c2[i] as int * c1[0] as int,

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed in main function */
    if c1.len() == 0 || c2.len() == 0 {
        return vec![0i8];
    }
    
    let result_len = c1.len() + c2.len() - 1;
    let mut result = Vec::with_capacity(result_len);
    
    let mut k = 0usize;
    while k < result_len
        invariant
            0 <= k <= result_len,
            result_len == c1.len() + c2.len() - 1,
            c1.len() > 0,
            c2.len() > 0,
            result.len() == k,
        decreases result_len - k
    {
        let coeff = poly_coeff(&c1, &c2, k);
        result.push(coeff as i8);
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}