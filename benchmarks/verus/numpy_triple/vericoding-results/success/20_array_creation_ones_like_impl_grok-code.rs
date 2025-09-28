// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ones_like<T>(a: &Vec<T>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): added decreases clause to while loop for termination */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i >= 0 && i <= a.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 1,
        decreases a.len() - i
    {
        result.push(1);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}