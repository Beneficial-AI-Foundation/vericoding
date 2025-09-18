// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): new_vec with usize for size parameter */
fn new_vec(size: usize, default_value: f64) -> (vec: Vec<f64>)
{
    let mut vec = Vec::new();
    let mut i: usize = 0;
    while i < size
        invariant
            vec.len() == i,
            0 <= i <= size,
    {
        vec.push(default_value);
        i = i + 1;
    }
    vec
}
// </vc-helpers>

// <vc-spec>
fn hermemul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0) || 
        (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0) 
        ==> (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replaced ghost types with concrete types */
{
    let l1 = c1.len();
    let l2 = c2.len();
    let result_len_usize = l1 + l2 - 1;
    let mut result_vec = new_vec(result_len_usize, 0.0);
    let mut i: usize = 0;
    while i < l1
        invariant
            0 <= i <= l1,
            result_vec.len() == result_len_usize,
            c1.len() == l1,
            c2.len() == l2,
            result_len_usize == l1 + l2 - 1,
    {
        let mut j: usize = 0;
        while j < l2
            invariant
                0 <= j <= l2,
                0 <= i < l1,
                result_vec.len() == result_len_usize,
                c1.len() == l1,
                c2.len() == l2,
                result_len_usize == l1 + l2 - 1,
        {
            let index = i + j;
            result_vec.set(index, result_vec[index] + c1[i] * c2[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}