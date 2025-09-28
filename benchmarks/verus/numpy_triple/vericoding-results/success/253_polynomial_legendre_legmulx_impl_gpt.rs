// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helpers_marker() {}
// </vc-helpers>

// <vc-spec>
fn legmulx(c: Vec<f32>) -> (result: Vec<f32>)
    requires c@.len() > 0,
    ensures
        result@.len() == c@.len() + 1,
        result[0] == 0.0f32,
        result[1] == c[0],
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let mut result: Vec<f32> = Vec::new();
    result.push(0.0f32);
    let mut i: usize = 0;
    while i < n
        invariant
            c@.len() == n as int,
            0 <= i <= n,
            result@.len() == 1 + i as int,
            result@[0] == 0.0f32,
            forall|j: int| 0 <= j && j < i as int ==> result@[1 + j] == c@[j],
        decreases n - i
    {
        result.push(c[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}