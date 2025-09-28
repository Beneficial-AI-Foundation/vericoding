// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to first while loop and fixed typo in second loop invariant */
    if n == 0 {
        return 0;
    }

    let mut low: usize = 0;
    let mut high: usize = 1;

    // Find an upper bound for the square root
    while high <= n / high
        invariant
            low <= high,
            low * low <= n,
            high * high <= n,
        decreases n - high * high
    {
        let old_high = high;
        low = old_high;
        high = old_high * 2;
    }

    // Now we have low*low<=n and high*high>n
    while low + 1 < high
        invariant
            low <= high,
            low * low <= n,
            high * high > n,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if mid <= n / mid {
            low = mid;
        } else {
            high = mid;
        }
    }

    low
}
// </vc-code>

}
fn main() {}