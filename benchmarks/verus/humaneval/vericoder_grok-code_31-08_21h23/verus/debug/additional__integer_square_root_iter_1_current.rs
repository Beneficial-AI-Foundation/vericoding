use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut low = 1i32;
    let mut high = n;
    while low <= high {
        let mid = low + (high - low) / 2;
        if (mid as i64) * (mid as i64) <= (n as i64) {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    proof {
        assert((high as i64) * (high as i64) <= (n as i64));
        assert((high as i64 + 1) * (high as i64 + 1) > (n as i64));
    }
    high
}
// </vc-code>

fn main() {}
}