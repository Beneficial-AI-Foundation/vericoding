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
/* code modified by LLM (iteration 5): fixed invariant syntax */
    let mut low = 0;
    let mut high = n;
    
    while low + 1 < high 
        invariant 0 <= low < high <= n + 1
        invariant low * low <= n
        invariant n < high * high
    {
        let mid = low + (high - low) / 2;
        if mid * mid <= n {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    low
// </vc-code>

}
fn main() {}