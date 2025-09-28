use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn quotient_rec(x: nat, y: nat) -> (r: int, q: int)
    requires
        y != 0,
    ensures
        q * y + r == x && 0 <= r < y && 0 <= q,
    decreases
        x,
{
    if x < y {
        (x as int, 0)
    } else {
        let (r0, q0) = quotient_rec(x - y, y);
        (r0, q0 + 1)
    }
}
// </vc-helpers>

// <vc-spec>
proof fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
// </vc-spec>
// <vc-code>
{
    quotient_rec(x, y)
}
// </vc-code>

fn main() {
}

}