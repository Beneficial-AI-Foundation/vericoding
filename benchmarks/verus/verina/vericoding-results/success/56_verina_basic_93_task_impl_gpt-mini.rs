// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): returns swapped pair with ensures */
fn swap_helper(x: u8, y: u8) -> (res: (u8, u8))
    ensures
        res.0 == y && res.1 == x,
        x != y ==> (res.0 != x && res.1 != y),
{
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
    /* code modified by LLM (iteration 2): call helper and return swapped result */
    let result = swap_helper(x, y);
    result
}
// </vc-code>

}
fn main() {}