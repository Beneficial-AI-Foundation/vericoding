// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_f32(a: f32, b: f32) -> (res: f32)
    ensures
        res == a || res == b,
{
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn fmin(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x@.len() == y@.len(),
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] result@[i] == x@[i] || #[trigger] result@[i] == y@[i]
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            x@.len() == y@.len(),
            result@.len() == i as int,
            i <= x@.len(),
            forall|j: int| 0 <= j < i as int ==> (#[trigger] result@[j] == x@[j] || #[trigger] result@[j] == y@[j]),
        decreases x.len() - i
    {
        let min_val = min_f32(x[i], y[i]);
        result.push(min_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}