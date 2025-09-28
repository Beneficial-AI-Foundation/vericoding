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
    /* code modified by LLM (iteration 5): Added overflow bounds and fixed invariants */
    if n == 0 {
        return 0;
    }
    
    let mut low = 0usize;
    let mut high = if n < usize::MAX { n + 1 } else { n };
    
    while low + 1 < high
        invariant
            low * low <= n,
            high * high > n,
            low < high,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if mid <= 65535 && mid * mid <= n {
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