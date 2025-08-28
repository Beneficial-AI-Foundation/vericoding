use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn multiply(a: int, b: int) -> (result: int)
    ensures result == a * b
// </vc-spec>
// </vc-spec>

// <vc-code>
fn multiply(a: int, b: int) -> (result: int)
    ensures result == a * b
{
    a * b
}
// </vc-code>

fn main() {}

}