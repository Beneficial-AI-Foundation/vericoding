// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove comma after last requires clause */
fn add_vectors_element(a: &Vec<i32>, b: &Vec<i32>, i: int) -> i32
    requires a.len() == b.len(),
    requires 0 <= i && i < a.len()
{
    a[i] + b[i]
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed */
{
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    let mut i = 0;
    
    while i < n
        invariant 0 <= i <= n,
        invariant result.len() == i,
        invariant forall|j: int| 0 <= j && j < i ==> result[j] == add_vectors_element(a, b, j),
    {
        result.push(add_vectors_element(a, b, i));
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}