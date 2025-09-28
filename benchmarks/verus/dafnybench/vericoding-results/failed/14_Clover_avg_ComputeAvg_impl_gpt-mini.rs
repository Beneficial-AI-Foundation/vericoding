use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    return (a + b) / 2;
}
// </vc-code>

fn main() {
}

}