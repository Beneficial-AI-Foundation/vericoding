// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using `@` for sequence indexing instead of `view_nth` on `Vec`s. */
{
    let mut result_vec: Vec<i32> = Vec::new();
    let len = a.len();

    while result_vec.len() < len
        invariant
            result_vec.len() <= len,
            result_vec.len() <= a.len(),
            result_vec.len() <= b.len(),
            forall|k: int| 0 <= k < result_vec.len() ==> result_vec@[k] == a@[k] + b@[k],
        decreases len - result_vec.len()
    {
        let i: usize = result_vec.len();
        result_vec.push(a[i] + b[i]);
    }
    result_vec
}
// </vc-code>

}
fn main() {}