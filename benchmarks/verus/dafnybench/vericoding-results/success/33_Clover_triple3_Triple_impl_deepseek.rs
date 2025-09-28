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
  x * 3
}
// </vc-code>

fn main() {
}

}