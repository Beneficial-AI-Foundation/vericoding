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
    a * b
}
// </vc-code>

fn main() {}

}