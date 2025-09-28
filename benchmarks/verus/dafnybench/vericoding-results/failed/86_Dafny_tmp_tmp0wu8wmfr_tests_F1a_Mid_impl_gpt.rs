use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mid(p: int, q: int) -> (m: int)
    // | ... | ??? | ... |
    //        p m   q
    requires 
        p <= q,
    ensures 
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
// </vc-spec>
// <vc-code>
{
    let m = p + (q - p) / 2;
    proof {
        let d = q - p;
        assert(d >= 0);
        let k = d / 2;
        assert(m == p + k);
        assert(0 < 2);
        assert(d == (d / 2) * 2 + d % 2);
        assert(d == 2 * k + d % 2);
        assert(0 <= d % 2);
        assert(d % 2 < 2);

        assert(0 <= k);
        assert(p <= m);

        assert(d - 2 * k == d % 2);
        assert(2 * k <= d);
        assert(k <= 2 * k);
        assert(k <= d);

        assert(q == p + d);
        assert(m <= q);

        assert(m - p == k);
        assert(q - m == d - k);
        assert(k <= d - k);
        assert(m - p <= q - m);

        assert((q - m) - (m - p) == (d - k) - k);
        assert((q - m) - (m - p) == d - 2 * k);
        assert((q - m) - (m - p) == d % 2);
        assert(0 <= (q - m) - (m - p));
        assert((q - m) - (m - p) < 2);
        assert((q - m) - (m - p) <= 1);
    }
    m
}
// </vc-code>

fn main() {
}

}