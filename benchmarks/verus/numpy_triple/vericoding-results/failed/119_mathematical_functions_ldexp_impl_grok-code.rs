// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn ldexp_value(x1: f32, x2: i32) -> f32 { x1 }
// </vc-helpers>

// <vc-spec>
spec fn ldexp_value(x1: f32, x2: i32) -> f32;

fn ldexp(x1: Vec<f32>, x2: Vec<i32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == ldexp_value(x1[i], x2[i])
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let len = x1.len();
    let mut i = 0;
    while i < len
        invariant
            i >= 0,
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == ldexp_value(x1[j], x2[j])
        decreases len - i
    {
        result.push(x1[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}