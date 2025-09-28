// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 4): Added a `decreases` clause to the `while` loop, as required by the Verus verifier. The `decreases` clause is `high - low`, which decreases in each iteration. */
{
    let mut low: i32 = 0;
    let mut high: i32 = n;
    let mut ans: i32 = 0;

    while low <= high
        invariant
            0 <= low,
            0 <= high,
            0 <= ans,
            ans * ans <= n,
            low <= high + 1,
            high >= low - 1,
            // At the start of the loop, ans is the largest integer whose square is less than or equal to `n` found so far within the range [0, low-1]
            // And for any x in [high+1, n], x*x > n
            ans * ans <= n,
            low <= n + 1,
            high >= 0
        decreases high - low
    {
        let mid: i32 = low + (high - low) / 2;
        if mid * mid <= n {
            ans = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    ans
}
// </vc-code>

}
fn main() {}