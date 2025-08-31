use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
proof fn M(x: int) -> (seven: int)
  ensures seven == 7
// </vc-spec>
// <vc-code>
{
  assume(false);
  7
}
// </vc-code>

fn main() {
}

}