// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_vec_len_nonnegative<T>(v: Vec<T>)
    ensures
        v.len() >= 0,
{
}

proof fn lemma_vec_value_at_index<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v@.index(i) == v[i],
{
}

proof fn lemma_vec_all_zero_implies_element_zero<T>(v: Vec<T>, i: int)
    requires
        v@.index(i) == 0,
    ensures
        v[i] == 0,
{
}

proof fn lemma_hermmul_zero_case(c1: Vec<i32>, c2: Vec<i32>, result: Vec<i32>)
    requires
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0),
    ensures
        forall|k: int| 0 <= k < result.len() ==> result@.index(k) == 0,
{
}

proof fn lemma_hermmul_single_coeff_case(c1: Vec<i32>, c2: Vec<i32>, result: Vec<i32>)
    requires
        c2.len() == 1 && c1.len() > 0,
    ensures
        forall|i: int| 0 <= i < c1.len() ==> result@.index(i) == c1@.index(i) * c2@.index(0),
{
}
// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] == c1[i] * c2[0],
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] == c2[i] * c1[0],

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed array indexing issues in implementation */
    if c1.is_empty() || c2.is_empty() {
        vec![0]
    } else {
        let mut result = vec![0; c1.len() + c2.len() - 1];
        
        for i in 0..c1.len() {
            for j in 0..c2.len() {
                let idx = i + j;
                result[idx] += c1[i] * c2[j];
            }
        }
        
        result
    }
}
// </vc-code>

}
fn main() {}