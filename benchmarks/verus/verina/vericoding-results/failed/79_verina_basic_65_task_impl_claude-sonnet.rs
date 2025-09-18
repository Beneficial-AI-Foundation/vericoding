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
    /* code modified by LLM (iteration 5): simplified logic with proper initialization and bounds checking */
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = n;
    
    // Ensure high is valid
    while high > 0 && high <= usize::MAX / high && high * high < n {
        high = high * 2;
        if high > usize::MAX / 2 {
            high = usize::MAX;
            break;
        }
    }
    
    // If high^2 would overflow, find a safe upper bound
    if high > usize::MAX / high {
        high = 65536; // sqrt(usize::MAX) approximation for 64-bit
        while high > 0 && high <= usize::MAX / high && high * high < n {
            high = high + 1;
        }
    }
    
    while low + 1 < high
        invariant
            low * low <= n,
            high <= usize::MAX / high,
            n < high * high,
            low < high,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if mid <= usize::MAX / mid {
            let mid_squared = mid * mid;
            if mid_squared <= n {
                low = mid;
            } else {
                high = mid;
            }
        } else {
            high = mid;
        }
    }
    
    low
}
// </vc-code>

}
fn main() {}