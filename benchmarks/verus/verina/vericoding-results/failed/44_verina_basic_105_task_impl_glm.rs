// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added decreases clause to loop */
{
    let mut result = Vec::new();
    let n = a.len();
    let mut i = 0usize;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] * b[j],
        decreases n - i,
    {
        result.push(a[i] * b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}