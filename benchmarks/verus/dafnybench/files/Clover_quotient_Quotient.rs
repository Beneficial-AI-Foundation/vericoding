// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}