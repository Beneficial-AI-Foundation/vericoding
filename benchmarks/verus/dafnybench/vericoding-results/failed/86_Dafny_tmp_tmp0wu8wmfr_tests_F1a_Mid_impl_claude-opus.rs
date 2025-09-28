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
    let m = (p + q) / 2;
    
    proof {
        // Since p <= q, we have p + q >= 2p, so (p + q) / 2 >= p
        assert((p + q) / 2 >= p);
        
        // Since p <= q, we have p + q <= 2q, so (p + q) / 2 <= q
        assert((p + q) / 2 <= q);
        
        // The key property: 2m = p + q when q - p is even, or 2m = p + q - 1 when q - p is odd
        // This gives us m - p <= q - m
        assert(2 * m <= p + q);
        assert(m - p <= q - m);
        
        // For the difference bound
        assert(2 * m >= p + q - 1);
        assert((q - m) - (m - p) == q + p - 2 * m);
        assert(0 <= q + p - 2 * m <= 1);
    }
    
    m
}
// </vc-code>

fn main() {
}

}