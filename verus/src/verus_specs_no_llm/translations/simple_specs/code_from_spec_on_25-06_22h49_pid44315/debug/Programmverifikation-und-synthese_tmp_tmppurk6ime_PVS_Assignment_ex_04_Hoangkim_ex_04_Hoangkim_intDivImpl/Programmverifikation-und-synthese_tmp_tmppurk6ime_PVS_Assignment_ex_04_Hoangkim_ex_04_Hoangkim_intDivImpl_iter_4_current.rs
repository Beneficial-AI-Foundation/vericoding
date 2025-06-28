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
    
    // At this point, either remainder < d OR quotient == n/2
    if remainder < d {
        // Normal case: we have a valid division
        (quotient, remainder)
    } else {
        // remainder >= d but quotient == n/2 (can't increase quotient further)
        // We need to find a solution where q <= n/2 and r < d
        
        // Key insight: we need to potentially reduce quotient to ensure r < d
        let mut final_q = quotient;
        let mut final_r = remainder;
        
        // Reduce quotient until remainder < d
        while final_r >= d && final_q > 0
            invariant
                d * final_q + final_r == n,
                final_q >= 0,
                final_r >= 0,
                final_q <= n/2,
        {
            final_q = final_q - 1;
            final_r = final_r + d;
        }
        
        // Now we have either final_r < d OR final_q == 0
        if final_r < d {
            (final_q, final_r)
        } else {
            // final_q == 0 and final_r >= d
            // This means final_r == n and n >= d
            // Since n >= d and d > 0, we have n >= d
            // We need r < d, so let's set q = 1 if possible
            if n >= 2 * d && 1 <= n/2 {
                // We can use q = 1
                (1, n - d)
            } else if n < 2 * d {
                // n = d (since n >= d and n < 2*d, so d <= n < 2*d)
                // The only solution is q = 1, r = 0 (since d*1 + 0 = d = n)
                // But we need to check if 1 <= n/2
                // Since n >= d and d > 0, we have n >= 1
                // If n = d, then we need 1 <= d/2, which means d >= 2
                
                if d >= 2 {
                    // n >= d >= 2, so n/2 >= d/2 >= 1
                    (1, n - d)
                } else {
                    // d = 1, so n >= 1. If n = 1, then n/2 = 0.5, so 1 > n/2
                    // In this case, we must use q = 0
                    // But then r = n >= d = 1, which violates r < d
                    // This suggests the specification might be unsatisfiable in some cases
                    
                    // Let's try the maximum possible quotient that keeps r < d
                    // We want the largest q <= n/2 such that n - d*q < d
                    // This means n - d < d*q, so q > (n-d)/d
                    // Since d = 1, we need q > n-1, so q >= n (since q is integer)
                    // But we also need q <= n/2
                    // This is only possible if n <= n/2, which means n <= 0
                    // But we have n >= d = 1 > 0, contradiction
                    
                    // The specification seems unsatisfiable in this case
                    // Let's return q=0, r=n and let verification fail if needed
                    (0, n)
                }
            } else {
                // This case should not happen given our constraints
                (0, n)
            }
        }
    }
}

}