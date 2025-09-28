use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty helpers as not needed for this verification
// </vc-helpers>

// <vc-spec>
proof fn triple(x: int) -> (r: int)
  ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
    3 * x
}
// </vc-code>

fn main() {
}

}