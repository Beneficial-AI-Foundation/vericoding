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
/* code modified by LLM (iteration 5): removed incorrect proof block wrapper from executable code */
{
    let mut r: int = x as int;
    let mut q: int = 0;

    while r >= y as int
        invariant
            x as int == q * (y as int) + r,
            0 <= r,
            0 <= q,
            y > 0,
        decreases r
    {
        r = r - (y as int);
        q = q + 1;
    }
    (r, q)
}
// </vc-code>

}
fn main() {}