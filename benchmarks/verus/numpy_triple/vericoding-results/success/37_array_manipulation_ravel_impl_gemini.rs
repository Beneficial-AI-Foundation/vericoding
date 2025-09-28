// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ravel(a: Vec<f32>) -> (result: Vec<f32>)
    ensures result@ == a@
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result@ == a@.subrange(0, i as int),
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}