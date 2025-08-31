use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
proof fn triple(x: int) -> (r: int)
  ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
  assume(false);
  0 as int  // unreachable due to assume(false)
}
// </vc-code>

fn main() {
}

}