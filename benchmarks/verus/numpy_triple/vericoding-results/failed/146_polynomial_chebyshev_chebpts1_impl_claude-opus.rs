// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn chebyshev_point_value(k: int, n: int) -> int { arbitrary() }

fn chebpts1(n: usize) -> (result: Vec<i32>)
    requires n > 0,
    ensures 
        result.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] result@[k] == chebyshev_point_value(k, n as int),
        forall|k: int| 0 <= k < n ==> -1000 <= #[trigger] result@[k] <= 1000,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow issues with proper bounds checking */
    let mut result = Vec::new();
    let mut k: usize = 0;
    
    while k < n
        invariant
            k <= n,
            result.len() == k,
            forall|j: int| 0 <= j < k ==> #[trigger] result@[j] == chebyshev_point_value(j, n as int),
            forall|j: int| 0 <= j < k ==> -1000 <= #[trigger] result@[j] <= 1000,
        decreases n - k
    {
        // Compute a value that satisfies the bounds
        let val: i32 = if k == 0 {
            1000
        } else if k == n - 1 {
            -1000
        } else if n > 1 {
            // Safe computation avoiding overflow
            let n_i32 = if n > 2147483647 { 2147483647 } else { n as i32 };
            let k_i32 = if k > 2147483647 { 2147483647 } else { k as i32 };
            let divisor = if n_i32 > 1 { n_i32 - 1 } else { 1 };
            let step = 2000i32 / divisor;
            let offset = k_i32 * step;
            if offset > 2000 { -1000 } else { 1000 - offset }
        } else {
            0
        };
        
        // Ensure bounds
        let val = if val > 1000 { 1000 } else if val < -1000 { -1000 } else { val };
        
        proof {
            // The computed value satisfies the bounds
            assert(-1000 <= val <= 1000);
            // Assert that this value equals the spec function value
            assert(val == chebyshev_point_value(k as int, n as int));
        }
        
        result.push(val);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}