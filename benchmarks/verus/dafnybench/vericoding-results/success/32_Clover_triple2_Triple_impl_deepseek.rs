use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn triple_lemma(x: int)
    ensures
        3 * x == x + x + x,
{
    assert(3 * x == x + x + x) by(nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
proof fn triple(x: int) -> (r: int)
  ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
    x + x + x
}
// </vc-code>

fn main() {
}

} // verus!