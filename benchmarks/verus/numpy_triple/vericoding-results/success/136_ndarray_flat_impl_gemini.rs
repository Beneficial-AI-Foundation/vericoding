// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_flat(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to prove loop termination */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            result@ == a@.subrange(0, i as int),
        decreases a.len() - i,
    {
        let element = a[i];
        result.push(element);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}