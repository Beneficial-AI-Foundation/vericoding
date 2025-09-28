use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
proof fn M(x: int) -> (seven: int)
  ensures seven == 7
// </vc-spec>
// <vc-code>
{
  let seven: int = 7;
  assert(seven == 7);
  seven
}
// </vc-code>

fn main() {
}

}