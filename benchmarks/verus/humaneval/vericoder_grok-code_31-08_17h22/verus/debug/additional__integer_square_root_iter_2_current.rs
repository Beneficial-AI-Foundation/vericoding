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
    let mut left: i64 = 0;
    let mut right: i64 = n as i64;
    while left < right
        invariant
            0 <= left <= right <= n as i64,
            left as i64 * left as i64 <= n as i64,
    {
        let mid: i64 = left + (right - left + 1) / 2;
        proof {
            assert(mid >= left && mid <= right);
        }
        if mid * mid <= n as i64 {
            left = mid;
        } else {
            right = mid - 1;
        }
    }
    proof {
        assert(left as i64 * left as i64 <= n as i64);
        assert(n as i64 < (left + 1) as i64 * (left + 1) as i64);
    }
    return left as i32;
}
// </vc-code>

fn main() {}
}