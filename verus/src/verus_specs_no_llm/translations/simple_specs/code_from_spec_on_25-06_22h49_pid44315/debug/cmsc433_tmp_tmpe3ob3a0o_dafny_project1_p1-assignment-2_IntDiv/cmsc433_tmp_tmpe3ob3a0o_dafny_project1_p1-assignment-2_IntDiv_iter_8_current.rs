use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IntDiv(m: int, n: int) -> (d: int, r: int)
    requires
        n > 0
    ensures
        m == n * d + r && 0 <= r < n
{
    if m >= 0 {
        // For non-negative m, use standard division
        let mut q = 0;
        let mut rem = m;
        
        while rem >= n
            invariant
                n > 0,
                rem >= 0,
                m == n * q + rem
            decreases rem
        {
            q = q + 1;
            rem = rem - n;
        }
        
        (q, rem)
    } else {
        // For negative m, we need to find q such that m = n * q + r where 0 <= r < n
        // This means q = floor(m/n), which for negative m is more negative than m/n
        
        // Start with q = 0, rem = m (which is negative)
        let mut q = 0;
        let mut rem = m;
        
        // Decrease q and increase rem until rem is in [0, n)
        while rem < 0
            invariant
                n > 0,
                m == n * q + rem
            decreases 0 - rem
        {
            q = q - 1;
            rem = rem + n;
        }
        
        // At this point rem >= 0, but we need to ensure rem < n
        while rem >= n
            invariant
                n > 0,
                rem >= 0,
                m == n * q + rem
            decreases rem
        {
            q = q + 1;
            rem = rem - n;
        }
        
        (q, rem)
    }
}

}