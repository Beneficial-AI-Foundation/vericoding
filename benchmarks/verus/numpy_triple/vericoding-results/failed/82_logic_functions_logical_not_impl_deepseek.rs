// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed indexing syntax and return type */
fn safe_vec_index<T>(vec: &Vec<T>, i: usize) -> &T
    requires
        0 <= i < vec.len()
{
    &vec[i]
}
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed comparison by dereferencing and proper vector indexing */
{
    let len = x.len();
    let mut result = Vec::new();
    let mut n: usize = 0;

    while n < len
        invariant
            0 <= n <= len,
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == (x[i] == 0.0)
        decreases len - n
    {
        let current = *safe_vec_index(&x, n) == 0.0;
        result.push(current);
        n = n + 1;
    }
    result
}
// </vc-code>

}
fn main() {}