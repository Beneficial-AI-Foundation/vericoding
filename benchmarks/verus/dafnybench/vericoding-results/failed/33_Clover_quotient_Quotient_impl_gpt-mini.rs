use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
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
    let mut r: nat = x;
    let mut q: nat = 0;
    while r >= y
        invariant({ q * y + r == x && 0 <= q && 0 <= r })
        decreases r
    {
        r = r - y;
        q = q + 1;
    }
    let rr: int = r as int;
    let qq: int = q as int;
    proof {
        // from loop invariant: q * y + r == x
        assert(q * y + r == x);
        // loop termination gives r < y
        assert(r < y);
        // cast equality to ints
        assert(qq * (y as int) + rr == (x as int));
        assert(0 <= rr);
        assert(rr < (y as int));
        assert(0 <= qq);
    }
    (rr, qq)
}
// </vc-code>

fn main() {
}

}