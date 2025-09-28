use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn quotient_rec(x: nat, y: nat) -> (res: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = res;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
    decreases x
{
    if x < y {
        let r: int = x as int;
        let q: int = 0;
        assert(0 <= r && r < y);
        assert(0 <= q);
        assert(q * y + r == x);
        (r, q)
    } else {
        assert(0 < y);
        assert(x - y < x);
        let (r2, q2) = quotient_rec(x - y, y);
        let r: int = r2;
        let q: int = q2 + 1;
        assert(0 <= r && r < y);
        assert(0 <= q2);
        assert(0 <= q);
        assert(q2 * y + r2 == x - y);
        assert(q * y + r == q2 * y + r2 + y);
        assert(q * y + r == (x - y) + y);
        assert(q * y + r == x);
        (r, q)
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