use vstd::prelude::*;

verus! {

// <vc-helpers>
use core::ops::{Div, Rem};
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
    let diff: int = q - p;
    let m_minus_p: int = diff / 2; // Use Verus integer division
    let m: int = p + m_minus_p;

    proof {
        assert(diff >= 0) by (nonlinear_arith); // Follows from p <= q
        assert(m_minus_p == (q - p) / 2) by (nonlinear_arith); // By definition

        // Prove p <= m <= q
        assert(m - p == (q - p) / 2) by (nonlinear_arith);
        assert((q - p) / 2 >= 0) by (nonlinear_arith); // Since q-p >= 0
        assert(m >= p) by (nonlinear_arith); // Since (q-p)/2 >= 0
        
        // m <= q
        // q - m == q - (p + (q - p) / 2)
        //          == q - p - (q - p) / 2
        //          == (q - p) - (q - p) / 2
        assert(q - m == q - (p + (q - p) / 2)) by (nonlinear_arith);
        assert(q - m == (q - p) - (q - p) / 2) by (nonlinear_arith); // simplifies
        assert(q - m == (q - p) / 2 + (q-p) % 2) by (nonlinear_arith);
        assert(q - m >= 0) by (nonlinear_arith);
        assert(m <= q) by (nonlinear_arith);

        // Prove m - p <= q - m
        assert(m - p == (q - p) / 2) by (nonlinear_arith);
        assert(q - m == (q - p) / 2 + (q-p) % 2) by (nonlinear_arith);
        assert(m - p <= q - m) by (nonlinear_arith);

        // Prove 0 <= (q - m) - (m - p) <= 1
        assert((q - m) - (m - p) == (q - m) - (q - p) / 2) by (nonlinear_arith);
        let remainder = diff % 2;
        if (remainder == 0) {
            assert((q - p) / 2 == (q - p) - (q - p) / 2) by (nonlinear_arith); // This is true if remainder is 0
            assert(q - m == (q - p) / 2) by (nonlinear_arith);
            assert((q - m) - (m - p) == 0) by (nonlinear_arith);
        } else { // remainder == 1
            assert((q - p) / 2 + 1 == (q - p) - (q - p) / 2) by (nonlinear_arith);
            assert(q - m == (q - p) / 2 + 1) by (nonlinear_arith);
            assert((q - m) - (m - p) == 1) by (nonlinear_arith);
        }
        assert(0 <= (q - m) - (m - p)) by (nonlinear_arith);
        assert((q - m) - (m - p) <= 1) by (nonlinear_arith);
    }
    m
}
// </vc-code>

fn main() {
}

}