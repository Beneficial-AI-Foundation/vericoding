// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
proof fn sqrt_approx(n: nat) -> (r: nat)
    ensures r * r <= n < (r + 1) * (r + 1)
{
    if n == 0 {
        0
    } else {
        let r = sqrt_approx((n - 1) as nat);
        if (r + 1) * (r + 1) <= n {
            r + 1
        } else {
            r
        }
    }
}

spec fn square(i: nat) -> nat {
    i * i
}
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat type usage in executable code */
    if n == 0 {
        true
    } else {
        let mut low: u64 = 0;
        let mut high: u64 = n;
        
        while low <= high
            invariant
                low <= high,
                low * low <= n,
                high * high >= n
            decreases high - low
        {
            let mid = low + (high - low) / 2;
            let square = mid * mid;
            
            if square == n {
                return true;
            } else if square < n {
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }
        
        false
    }
}
// </vc-code>

}
fn main() {}