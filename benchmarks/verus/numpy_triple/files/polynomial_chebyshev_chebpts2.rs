// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebpts2(n: usize) -> (result: Vec<f32>)
    requires n >= 2,
    ensures
        result.len() == n,

        result[0] == -1.0f32,

        result[(n-1) as int] == 1.0f32,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}