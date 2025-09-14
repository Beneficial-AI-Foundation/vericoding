// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use mathematical int for square to avoid i128/int mismatch */
spec fn sq_i128(x: int) -> int { x * x }
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): binary search using i32 indices and i128 for comparisons */
    let n_i128: i128 = n as i128;
    let mut lo: i32 = 0;
    let mut hi: i32 = n;
    while lo < hi
        invariant
            0 <= lo,
            lo <= hi,
            (lo as i128) * (lo as i128) <= n_i128,
            n_i128 < ((hi as i128) + 1) * ((hi as i128) + 1),
        decreases hi - lo
    {
        let mid: i32 = (lo + hi + 1) / 2;
        proof {
            assert(lo < hi);
            assert(mid > lo);
            assert(mid <= hi);
        }
        if (mid as i128) * (mid as i128) <= n_i128 {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}
// </vc-code>

}
fn main() {}