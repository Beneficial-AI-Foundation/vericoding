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
    /* code modified by LLM (iteration 5): fix type comparison error */
    if n == 0 {
        return 0;
    }
    
    if n == usize::MAX {
        // Special case: sqrt(usize::MAX) is close to 2^32 on 64-bit systems
        // We need to find the largest k such that k*k <= usize::MAX
        let mut low: usize = 0;
        let mut high: usize = 1 << 32;  // Upper bound for sqrt(2^64)
        
        while low + 1 < high
            invariant
                low * low <= n,
                high <= (1 << 32),
                low < high,
            decreases high - low,
        {
            let mid = low + (high - low) / 2;
            if mid <= usize::MAX / mid && mid * mid <= n {
                low = mid;
            } else {
                high = mid;
            }
        }
        return low;
    }
    
    let mut low: usize = 0;
    let mut high: usize = n + 1;
    
    proof {
        assert(low * low == 0);
        assert(0 <= n);
        assert(low * low <= n);
        assert(n < n + 1);
        assert(high == n + 1);
        // For n < usize::MAX, we have n + 1 <= usize::MAX
        // and (n+1)*(n+1) > n for all n >= 0
        assert(n < high * high) by {
            if high <= usize::MAX / high {
                assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
                assert(n * n + 2 * n + 1 > n);
            }
        }
    }
    
    while low + 1 < high
        invariant
            low * low <= n,
            n < high * high,
            low < high,
            high <= n + 1,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        
        if mid <= usize::MAX / mid && mid * mid <= n {
            low = mid;
            proof {
                assert(low * low <= n);
            }
        } else {
            high = mid;
            proof {
                if mid > usize::MAX / mid {
                    // mid * mid would overflow, so it's > n
                    assert(n < high * high);
                } else {
                    assert(mid * mid > n);
                    assert(n < high * high);
                }
            }
        }
    }
    
    proof {
        assert(low + 1 >= high);
        assert(low < high);
        assert(low + 1 == high);
        assert(low * low <= n);
        assert(n < high * high);
        assert(high == low + 1);
        assert(n < (low + 1) * (low + 1));
    }
    
    low
}
// </vc-code>

}
fn main() {}