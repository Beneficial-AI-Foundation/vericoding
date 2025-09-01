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
    // impl-start
    let mut low: i32 = 0;
    let mut high: i32 = n;
    let mut ans: i32 = 0;

    while low <= high
        invariant
            low >= 0,
            high >= -1, // high can be -1 when n=0, high becomes -1
            ans * ans <= n,
            ans <= low,
            high + 1 >= low,
            high <= n,
            ans >= 0,
            n >= 1,
        decreases high - low
    {
        let mid: i32 = low + (high - low) / 2;

        if mid > n / mid {
            high = mid - 1;
        } else {
            ans = mid;
            low = mid + 1;
        }
    }
    ans
    // impl-end
}
// </vc-code>

fn main() {}
}