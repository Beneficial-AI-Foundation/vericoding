use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
proof fn triple(x: int) -> (r: int)
  ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
    let r = x + x + x;
    assert(r == x + x + x);
    assert(r == 3 * x);
    r
}
// </vc-code>

fn main() {
}

} // verus!