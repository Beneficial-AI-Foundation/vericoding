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
    let n_int: int = n as int;
    let mut left: int = 0;
    let mut right: int = n_int + 1;
    while left + 1 < right
        invariant
            0 <= left,
            left <= right,
            left * left <= n_int,
            n_int < right * right,
    {
        let mid: int = (left + right) / 2;
        if mid * mid <= n_int {
            left = mid;
        } else {
            right = mid;
        }
    }
    proof {
        assert(left * left <= n_int);
        let temp = left + 1;
        assert(n_int < temp * temp);
    }
    return left as i32;
}
// </vc-code>

fn main() {}
}