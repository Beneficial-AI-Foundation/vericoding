// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn pair_swap(x: u8, y: u8) -> (u8, u8) {
    (y, x)
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
    let result = (y, x);
    result
}
// </vc-code>

}
fn main() {}