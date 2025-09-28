// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mul(a: i8, b: i8) -> (result: i8)
    requires
        (a as int) * (b as int) >= i8::MIN as int,
        (a as int) * (b as int) <= i8::MAX as int,
    ensures
        (a as int) * (b as int) == result as int
{
    a * b
}
// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<Vec<i8>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] as int == a[i] as int * b[j] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected indexing for `a` and `b` to `i` and `j` in `mul` calls and fixed issues related to array indexing in loop invariants by converting `i` to `usize`. Fixed potential overflow/underflow issues in `mul` function by adding pre-condition checks. */
    let len_a = a.len();
    let len_b = b.len();

    let mut result_vec: Vec<Vec<i8>> = Vec::new();
    
    while result_vec.len() < len_a
        invariant
            result_vec.len() <= len_a,
            forall|i_idx: int| 0 <= i_idx < result_vec.len() ==> result_vec[i_idx].len() == len_b,
            forall|i_idx: int, j_idx: int| 0 <= i_idx < result_vec.len() && 0 <= j_idx < result_vec[i_idx].len() ==> 
                result_vec[i_idx][j_idx] as int == a[i_idx] as int * b[j_idx] as int,
        decreases len_a - result_vec.len()
    {
        let mut inner_vec: Vec<i8> = Vec::new();
        let i = result_vec.len() as usize;

        while inner_vec.len() < len_b
            invariant
                inner_vec.len() <= len_b,
                forall|k_idx: int| 0 <= k_idx < inner_vec.len() ==> 
                    inner_vec[k_idx] as int == a[i] as int * b[k_idx] as int,
            decreases len_b - inner_vec.len()
        {
            let j = inner_vec.len() as usize;
            inner_vec.push(mul(a[i], b[j]));
        }
        result_vec.push(inner_vec);
    }

    result_vec
}
// </vc-code>

}
fn main() {}