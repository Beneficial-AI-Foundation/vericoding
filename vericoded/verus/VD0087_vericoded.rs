use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn swap_bitvectors(x: u8, y: u8) -> (result: (u8, u8))
    ensures 
        result.0 == y,
        result.1 == x,
// </vc-spec>
// <vc-code>
{
    (y, x)
}
// </vc-code>

fn main() {
}

}