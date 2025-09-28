// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn asanyarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): use usize for loop index and sequence invariant */
{
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            result@ == a@.subrange(0, i as int),
        decreases a.len() - i,
    {
        result.push(a[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}