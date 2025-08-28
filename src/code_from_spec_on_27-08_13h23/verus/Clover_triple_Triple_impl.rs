use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers, spec functions, or proofs needed for this simple specification
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn triple(x: i32) -> (r: i32)
  ensures r == 3 * x
// </vc-spec>
// </vc-spec>

// <vc-code>
fn triple(x: i32) -> (r: i32)
    ensures r == 3 * x
{
    3 * x
}
// </vc-code>

fn main() {
}

}