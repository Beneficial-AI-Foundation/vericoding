use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let m: int = p + (q - p) / 2;
    proof {
        let d = q - p;
        // d >= 0 by precondition p <= q
        assert(d >= 0);
        let k = d / 2;
        // m = p + k
        assert(m == p + k);
        // k >= 0 (follows from d >= 0 and k == d/2)
        assert(k >= 0);
        // p <= m
        assert(p <= m);
        // relate d, k, and remainder
        let rem = d % 2;
        assert(0 <= rem);
        assert(rem < 2);
        assert(d == 2 * k + rem);
        // m <= q since 2*k <= d
        assert(2 * k <= d);
        assert(k <= d);
        assert(m <= q);
        // differences
        assert(m - p == k);
        assert(q - m == d - k);
        // m - p <= q - m  <=>  k <= d - k  <=> 2k <= d
        assert(m - p <= q - m);
        // (q - m) - (m - p) = (d - k) - k = d - 2k
        let diff = (q - m) - (m - p);
        assert(diff == d - 2 * k);
        // Let r = d - 2*k, then r == rem and 0 <= rem < 2 => 0 <= r <= 1
        let r = d - 2 * k;
        assert(r == rem);
        assert(0 <= r);
        assert(r <= 1);
    }
    m
}
// </vc-code>

fn main() {
}

}