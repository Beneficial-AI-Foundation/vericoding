// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helpers using mathematical integers to avoid division/type mismatches */
spec fn leq_square(lo: int, n: int) -> bool {
    lo >= 0 && lo * lo <= n
}
spec fn lt_square(hi: int, n: int) -> bool {
    hi > 0 && n < hi * hi
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): binary search with casted spec helpers to avoid division/type issues in proofs */
    if n == 0 {
        0
    } else {
        let mut lo: usize = 0;
        let mut hi: usize = if n == usize::MAX { n } else { n + 1 };
        proof {
            assert(leq_square(lo as int, n as int));
            assert(lt_square(hi as int, n as int));
            assert(lo <= hi);
        }
        while lo < hi - 1
            invariant
                leq_square(lo as int, n as int),
                lt_square(hi as int, n as int),
                lo <= hi,
            decreases hi - lo
        {
            let mid = lo + (hi - lo) / 2;
            if mid == 0 || mid <= n / mid {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        proof {
            assert(!(lo < hi - 1));
            assert(hi <= lo + 1);
            assert(leq_square(lo as int, n as int));
            assert(lt_square(hi as int, n as int));

            // show result * result <= n
            if lo == 0 {
                ()
            } else {
                assert((lo as int) * (lo as int) <= n as int);
                assert(((lo * lo) as int) <= n as int);
                assert(lo * lo <= n);
            }

            // show n < (lo + 1) * (lo + 1)
            assert(hi > 0);
            assert(n as int < (hi as int) * (hi as int));
            assert(hi as int <= (lo + 1) as int);
            assert(n as int < ((lo + 1) as int) * ((lo + 1) as int));
            assert(n < (lo + 1) * (lo + 1));
        }
        lo
    }
}
// </vc-code>

}
fn main() {}