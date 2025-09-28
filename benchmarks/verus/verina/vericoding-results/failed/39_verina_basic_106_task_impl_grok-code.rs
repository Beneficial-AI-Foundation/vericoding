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
{
    /* code modified by LLM (iteration 3): added decreases clause to loop for termination */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k] + b[k],
        decreases a.len() - i
    {
        result.push(a[i] + b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}