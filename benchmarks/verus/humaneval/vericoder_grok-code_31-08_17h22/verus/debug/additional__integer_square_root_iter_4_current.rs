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
    let n_int: i128 = n as i128;
    let mut left: i128 = 0;
    let mut right: i128 = n_int + 1;
    while left + 1 < right
        invariant
            0 <= left as int,
            (left as int) <= (right as int),
            (left as int) * (left as int) <= n as int,
            n as int < (right as int) * (right as int),
    {
        let mid: i128 = (left + right) / 2;
        if mid * mid <= n_int {
            left = mid;
        } else {
            right = mid;
        }
    }
    proof {
        assert((left as int) * (left as int) <= n as int);
        let temp = left as int + 1;
        assert(n as int < temp * temp);
    }
    return left as i32;
}
// </vc-code>

fn main() {}
}