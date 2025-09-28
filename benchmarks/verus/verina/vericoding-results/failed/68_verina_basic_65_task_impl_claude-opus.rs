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
    /* code modified by LLM (iteration 5): simplified binary search with overflow protection */
    if n == 0 {
        return 0;
    }
    
    let mut low: usize = 0;
    let mut high: usize = n;
    let mut result: usize = 0;
    
    // Find a safe upper bound
    if n >= 4 {
        high = n / 2;
        while high > 46340 // sqrt(usize::MAX) is approximately 46340 for 32-bit
            invariant
                high > 0,
                high <= n,
            decreases high
        {
            high = high / 2;
        }
    } else {
        high = n;
    }
    
    while low <= high
        invariant
            result * result <= n,
            n < (result + 1) * (result + 1) || low <= high,
            low <= high ==> low <= n,
            low <= high ==> high <= n,
            result <= n,
            result <= high || low > high,
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        // Safe multiplication check
        if mid <= 46340 && mid * mid <= n {
            result = mid;
            if mid * mid == n {
                return result;
            }
            low = mid + 1;
        } else {
            if mid > 0 {
                high = mid - 1;
            } else {
                return 0;
            }
        }
    }
    
    // Final check to ensure postcondition
    while result + 1 <= 46340 && (result + 1) * (result + 1) <= n
        invariant
            result * result <= n,
            result <= n,
        decreases n - result
    {
        result = result + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}