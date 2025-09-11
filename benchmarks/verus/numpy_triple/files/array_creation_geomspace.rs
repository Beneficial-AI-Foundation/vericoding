// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn geomspace(start: f64, stop: f64, n: usize, endpoint: bool) -> (result: Vec<f64>)
    requires 
        start != 0.0,
        stop != 0.0,
        n > 0,
    ensures
        result.len() == n,
        n > 0 ==> result[0] == start,
        (endpoint && n > 1) ==> result[(n - 1) as int] == stop,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}