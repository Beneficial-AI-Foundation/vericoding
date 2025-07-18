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
        {
            q = q + 1;
            rem = rem - n;
        }
        
        (q, rem)
    } else {
        // For negative m, we need to adjust to ensure 0 <= r < n
        let mut q = 0;
        let mut rem = m;
        
        // First, make rem non-negative by adjusting q downward
        while rem < 0
            invariant
                n > 0,
                m == n * q + rem
        {
            q = q - 1;
            rem = rem + n;
        }
        
        // Now rem >= 0, but we might need to reduce it further
        while rem >= n
            invariant
                n > 0,
                rem >= 0,
                m == n * q + rem
        {
            q = q + 1;
            rem = rem - n;
        }
        
        (q, rem)
    }
}

}