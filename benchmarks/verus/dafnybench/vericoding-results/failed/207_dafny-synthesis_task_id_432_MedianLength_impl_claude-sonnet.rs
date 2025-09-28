use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn median_length(a: int, b: int) -> (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    (a + b) / 2
}
// </vc-code>

fn main() {}

}