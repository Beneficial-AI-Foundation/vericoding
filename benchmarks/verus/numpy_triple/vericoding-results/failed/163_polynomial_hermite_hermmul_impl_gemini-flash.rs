// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type casting by converting `idx` to `usize` for vector indexing only when the `idx` is proven to be non-negative. Also, explicitly cast the comparison value `0` to `int` to match the type of `idx`. */
fn get_coeff(poly: &Vec<i8>, idx: int) -> i8
{
    if 0.int() <= idx && idx < poly.len() as int {
        poly[idx as usize]
    } else {
        0
    }
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
/* code modified by LLM (iteration 5): Corrected type inconsistencies by explicitly casting integer literals to `int` for comparisons and arithmetic operations involving `int` variables. This addresses compilation errors related to `int` and `usize` mismatch. Also, adjusted loop bounds and result vector sizing for consistency. */
{
    let l1 = c1.len(); // usize
    let l2 = c2.len(); // usize

    if l1 == 0 || l2 == 0 {
        return vec![0];
    }

    let result_len_int: int = l1 as int + l2 as int - 1;
    let mut result: Vec<i8> = vec![0; result_len_int as usize];

    let mut i: int = 0.int();
    while i < l1 as int
        invariant
            0.int() <= i && i <= l1 as int,
            result.len() == result_len_int as usize
    {
        let mut j: int = 0.int();
        while j < l2 as int
            invariant
                0.int() <= j && j <= l2 as int,
                result.len() == result_len_int as usize
        {
            let index = i + j;
            if index >= 0.int() && index < result_len_int {
                let current_coeff: i8 = result[index as usize];
                let term: i8 = get_coeff(&c1, i) * get_coeff(&c2, j);
                result[index as usize] = current_coeff + term;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}