use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty as no additional helpers are needed for verification
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        proof {
            assert(0 <= 1 * 1 && 1 * 1 <= 1 && 1 < (1 + 1) * (1 + 1));
        }
        return 1;
    }
    proof {
        let mut left: i32 = 0;
        let mut right: i32 = n;
        while left < right
            invariant
            0 <= left,
            right <= n,
        {
            let mid: i32 = left + (right - left + 1) / 2;
            if (mid as i64 * mid as i64) <= (n as i64) {
                left = mid;
            } else {
                right = mid - 1;
            }
        }
        assert((left as i64 * left as i64) <= (n as i64));
        assert(n as i64 < ((left + 1) as i64 * (left + 1) as i64));
    }
    return left;
}
// </vc-code>

fn main() {}
}