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
    let mut low = 0;
    let mut high = n;
    while low < high {
        invariant {
            low <= high,
            (low == 0 || low <= n / low),
            (high + 1) > n / (high + 1)
        }
        decreases high - low;
        let mid = (low + high + 1) / 2;
        if mid <= n / mid {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    low
}
// </vc-code>

fn main() {}
}