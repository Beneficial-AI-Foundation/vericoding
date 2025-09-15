// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */

// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant */
{
    let mut result_vec: Vec<i32> = Vec::new();
    let len = a.len();
    if len > 0 {
        let mut i: usize = 0;
        while i < len
            invariant len == a.len(),
            invariant i <= len,
            invariant result_vec.len() == i,
            invariant forall|j: int| 0 <= j < i ==> result_vec[j] == a.index(j) * b.index(j)
        {
            result_vec.push(a.index(i) * b.index(i));
            i = i + 1;
        }
    }
    result_vec
}
// </vc-code>

}
fn main() {}