// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added Copy constraint to type parameter T. */
fn get_element_at_index<T: Copy>(v: &Vec<T>, i: usize) -> (result: T)
    requires i < v.len(),
    ensures result == v[i as int],
{
    v[i]
}
// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): No change needed. */
{
    let mut result_vec = a.clone();
    result_vec.set(j, 60);
    result_vec
}
// </vc-code>

}
fn main() {}