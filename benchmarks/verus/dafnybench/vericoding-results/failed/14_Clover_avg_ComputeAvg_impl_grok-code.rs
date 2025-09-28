use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::spec]
fn spec_avg(a: int, b: int) -> int
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
return (a + b) / 2;
}
// </vc-code>

fn main() {
}

}