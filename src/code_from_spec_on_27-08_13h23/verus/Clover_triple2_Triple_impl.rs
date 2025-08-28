use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is a syntax error in the code section.
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn triple(x: int) -> (r: int)
  ensures r == 3 * x
// </vc-spec>
// </vc-spec>

// <vc-code>
proof fn triple(x: int) -> (r: int)
    ensures r == 3 * x
{
    3 * x
}
// </vc-code>

fn main() {
}

} // verus!