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
    while low <= high
        invariant low >= 1
        invariant high <= n
        invariant forall |x: i32| #[trigger] (1 <= x && x <= high) ==> (x as i64) * (x as i64) <= (n as i64)
        invariant forall |x: i32| #[trigger] (high < x && x <= n) ==> (x as i64) * (x as i64) > (n as i64)
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if (mid as i64) * (mid as i64) <= (n as i64) {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    proof {
        assert(high as i64 * high as i64 <= n as i64);
        assert((high + 1) as i64 * (high + 1) as i64 > n as i64);
    }
    high
}
// </vc-code>

fn main() {}
}