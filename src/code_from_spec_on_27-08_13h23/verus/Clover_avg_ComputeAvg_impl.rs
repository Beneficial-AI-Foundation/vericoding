use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this simple computation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
{
    let avg = (a + b) / 2;
    avg
}
// </vc-code>

fn main() {
}

}