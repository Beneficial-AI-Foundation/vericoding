// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper to check integer multiplication bounds */
fn safe_multiply(x: i32, y: i32) -> (result: i32)
    requires
        x as int * y as int >= i32::MIN as int,
        x as int * y as int <= i32::MAX as int,
    ensures
        result as int == x as int * y as int,
{
    x * y
}
// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix indexing syntax for sequences */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] * b@[j],
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(0 <= i < a@.len());
            assert(a.len() == b.len());
            assert(0 <= i < b@.len());
        }
        let product = a@.index(i) * b@.index(i);
        result.push(product);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}