// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ogrid(start: f32, stop: f32, n: usize) -> (result: Vec<f32>)
    requires n > 0,
    ensures 
        result.len() == n,
        (n == 1 ==> result[0] == start),
        (n > 1 ==> result[0] == start),
        (n > 1 ==> result[n - 1] == stop),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}