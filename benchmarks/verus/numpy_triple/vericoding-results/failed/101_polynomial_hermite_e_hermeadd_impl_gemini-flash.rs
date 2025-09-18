// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `coeff_vec` indexing using `i` (int) to avoid `usize` casting issues for Verus indexing which expects `int` argument. */
spec fn get_coeff(coeff_vec: &Vec<i32>, i: int) -> i32 { if 0 <= i && i < coeff_vec.len() { coeff_vec[i as usize] } else { 0 } }
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted `get_coeff` calls to pass the correct integer types for indexing. */
{
    let len1_usize = c1.len();
    let len2_usize = c2.len();
    let result_len_usize = if len1_usize >= len2_usize { len1_usize } else { len2_usize };
    let mut result_vec = Vec::new();
    let mut i: usize = 0;

    while i < result_len_usize
        invariant
            0 <= i,
            result_vec.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result_vec[j as usize] == get_coeff(&c1, j) + get_coeff(&c2, j)
    {
        let ghost j = i as int;
        let coeff1 = get_coeff(&c1, j);
        let coeff2 = get_coeff(&c2, j);
        result_vec.push(coeff1 + coeff2);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}