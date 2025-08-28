use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is in the code syntax
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn M(x: int) -> (seven: int)
  ensures seven == 7
// </vc-spec>
// </vc-spec>

// <vc-code>
proof fn M(x: int) -> (seven: int)
    ensures seven == 7
{
    7
}
// </vc-code>

fn main() {
}

}