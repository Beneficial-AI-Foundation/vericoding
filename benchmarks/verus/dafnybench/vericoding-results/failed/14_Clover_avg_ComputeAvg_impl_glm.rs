use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
{
    (a + b) / 2
}
// </vc-helpers>

// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    (a + b) / 2
}
// </vc-code>

fn main() {
}

}