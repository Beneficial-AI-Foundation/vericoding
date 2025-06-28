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
                m == n * q + rem,
                q >= 0
            decreases rem
        {
            q = q + 1;
            rem = rem - n;
        }
        
        assert(0 <= rem < n);
        assert(m == n * q + rem);
        (q, rem)
    } else {
        // For negative m, we need to adjust to ensure 0 <= r < n
        let mut q = 0;
        let mut rem = m;
        
        // First, make rem non-negative by adjusting q downward
        while rem < 0
            invariant
                n > 0,
                m == n * q + rem,
                rem <= 0
            decreases -rem
        {
            q = q - 1;
            rem = rem + n;
        }
        
        // After the first loop, rem >= 0, but we need to ensure rem < n
        // The loop condition rem < 0 is false, so rem >= 0
        // But rem might be >= n, so we need another loop
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
        
        // At this point: rem >= 0 (from first loop exit) and rem < n (from second loop condition)
        assert(rem >= 0 && rem < n);
        assert(m == n * q + rem);
        (q, rem)
    }
}

}