// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_neq_sym(x: u8, y: u8)
    ensures
        x != y ==> y != x
{
    if x != y {
        assert(y != x);
    }
}
// </vc-helpers>

// <vc-spec>
fn swap_bitvectors(x: u8, y: u8) -> (result: (u8, u8))
    ensures
        result.0 == y && result.1 == x,
        x != y ==> (result.0 != x && result.1 != y),
// </vc-spec>
// <vc-code>
{
    (y, x)
}
// </vc-code>

}
fn main() {}