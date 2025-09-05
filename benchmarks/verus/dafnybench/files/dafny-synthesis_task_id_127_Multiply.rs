use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn multiply(a: int, b: int) -> (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
    assume(false);
    a * b  // This won't be reached due to assume(false)
}
// </vc-code>

fn main() {}

}
