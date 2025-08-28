use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn M(x: int) -> (seven: int)
  ensures seven == 7
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  7
}
// </vc-code>

fn main() {
}

}