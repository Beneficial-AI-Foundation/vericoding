use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    let sum: int = a + b;
    let avg: int = sum / 2 as int;
    avg
}
// </vc-code>

fn main() {
}

}