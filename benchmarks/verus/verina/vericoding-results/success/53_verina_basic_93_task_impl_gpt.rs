// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn swapped_pair(x: u8, y: u8) -> (u8, u8) { (y, x) }
proof fn swap_pair_lemma(x: u8, y: u8)
    ensures
        swapped_pair(x, y).0 == y,
        swapped_pair(x, y).1 == x,
        x != y ==> (swapped_pair(x, y).0 != x && swapped_pair(x, y).1 != y)
{
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
    let a = y;
    let b = x;
    (a, b)
}
// </vc-code>

}
fn main() {}