use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    let mut lo: u128 = 0u128;
    let mut hi: u128 = (n as u128) + 1u128;
    let n128: u128 = n as u128;

    // Help the verifier see the initial invariants
    proof {
        assert(lo < hi);
        assert(lo * lo <= n128);
        assert(n128 < hi * hi);
        assert(hi <= (n128 + 1u128));
    }

    while (lo + 1u128 < hi)
        invariant { lo < hi; }
        invariant { lo * lo <= n128; }
        invariant { n128 < hi * hi; }
        invariant { hi <= (n128 + 1u128); }
        decreases hi - lo;
    {
        let mid: u128 = lo + (hi - lo) / 2u128;

        // Prove lo < mid < hi
        proof {
            // from lo + 1 < hi we get hi >= lo + 2
            assert(hi >= lo + 2u128);
            // hence hi - lo >= 2
            assert(hi - lo >= 2u128);
            // so (hi - lo) / 2 >= 1
            assert((hi - lo) / 2u128 >= 1u128);
            // therefore mid = lo + (hi-lo)/2 >= lo + 1
            assert(mid == lo + (hi - lo) / 2u128);
            assert(mid >= lo + 1u128);
            assert(mid > lo);
            // and (hi - lo) / 2 < (hi - lo), so mid < hi
            assert((hi - lo) / 2u128 < (hi - lo));
            assert(mid < hi);
        }

        if mid * mid <= n128 {
            lo = mid;
            proof {
                // preserve invariants
                assert(lo < hi);
                assert(lo * lo <= n128);
                assert(n128 < hi * hi);
                assert(hi <= (n128 + 1u128));
            }
        } else {
            hi = mid;
            proof {
                // preserve invariants
                assert(lo < hi);
                assert(lo * lo <= n128);
                assert(n128 < hi * hi);
                assert(hi <= (n128 + 1u128));
            }
        }
    }

    proof {
        // ensure cast to u32 is safe
        // From lo*lo <= n128 and lo >= 0 we can deduce lo <= n128
        // Proof by cases on lo == 0 or lo >= 1
        if lo == 0u128 {
            assert(lo <= n128);
        } else {
            // lo >= 1 => lo * lo >= lo, so lo <= n128
            assert(lo * lo >= lo);
            assert(lo <= n128);
        }
        assert(n128 <= (u32::MAX as u128));
    }

    let r: u32 = lo as u32;
    proof {
        // At loop exit, lo < hi and not (lo + 1 < hi) => hi == lo + 1
        assert(lo + 1u128 >= hi);
        assert(lo < hi);
        assert(hi == lo + 1u128);
        // Now lo*lo <= n128 < (lo+1)*(lo+1)
        assert(lo * lo <= n128);
        assert(n128 < (lo + 1u128) * (lo + 1u128));
        // Casted versions for the postcondition
        assert((r as u128) * (r as u128) <= n128);
        assert(n128 < ((r as u128) + 1u128) * ((r as u128) + 1u128));
    }

    r
}
// </vc-code>

fn main() {}

}