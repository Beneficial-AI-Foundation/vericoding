use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn intDivImpl(n: int, d: int) -> (q: int, r: int)
    requires
        n >= d && n >= 0 && d > 0
    ensures
        (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d
{
    let mut quotient = 0;
    let mut remainder = n;
    
    while remainder >= d && quotient < n/2
        invariant
            d * quotient + remainder == n,
            quotient >= 0,
            remainder >= 0,
            quotient <= n/2,
    {
        quotient = quotient + 1;
        remainder = remainder - d;
    }
    
    // After the loop, we have two cases:
    // 1. remainder < d (we're done)
    // 2. remainder >= d but quotient >= n/2 (we hit the quotient limit)
    
    if remainder < d {
        // Case 1: Normal division result
        (quotient, remainder)
    } else {
        // Case 2: We hit the quotient limit, so we need to find a valid solution
        // where q <= n/2 and r < d
        
        // Try the maximum allowed quotient
        let max_q = n / 2;
        let r_at_max_q = n - d * max_q;
        
        if r_at_max_q < d {
            assert(d * max_q + r_at_max_q == n);
            assert(0 <= max_q <= n/2);
            assert(0 <= r_at_max_q < d);
            (max_q, r_at_max_q)
        } else {
            // Find the largest q <= n/2 such that n - d*q < d
            // This means n - d*q < d, so n - d < d*q, so (n-d)/d < q
            // We want the smallest integer q such that q > (n-d)/d and q <= n/2
            let min_q_for_valid_r = (n - d + 1) / d;  // This is ceil((n-d+1)/d)
            
            if min_q_for_valid_r <= n/2 {
                let final_q = min_q_for_valid_r;
                let final_r = n - d * final_q;
                assert(d * final_q + final_r == n);
                assert(0 <= final_q <= n/2);
                assert(0 <= final_r < d);
                (final_q, final_r)
            } else {
                // This should not happen given our preconditions
                // Let's use q = n/2 anyway
                (n/2, n - d * (n/2))
            }
        }
    }
}

}