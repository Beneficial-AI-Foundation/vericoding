use vstd::prelude::*;

verus! {
    // Method 1: Linear search from 0 upward - Cost O(sqrt(n))
    fn mroot1(n: u32) -> (r: u32)
        requires n >= 0,
        ensures 
            r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
    {
        let mut r: u32 = 0;
        while r * r <= n && (r + 1) * (r + 1) <= n
            invariant r * r <= n
            /* code modified by LLM (iteration 3): added decreases clause to prove termination */
            decreases n - r * r
        {
            r = r + 1;
        }
        r
    }

    // Method 2: Linear search from n downward - Cost O(n)
    fn mroot2(n: u32) -> (r: u32)
        requires n >= 0,
        ensures 
            r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
    {
        let mut r: u32 = n;
        while r * r > n
            invariant r <= n
            /* code modified by LLM (iteration 3): added decreases clause to prove termination */
            decreases r
        {
            r = r - 1;
        }
        r
    }

    // Method 3: Binary search - Cost O(log n)
    fn mroot3(n: u32) -> (r: u32)
        requires 
            n >= 0,
            n < 0xFFFF_FFFE,
        ensures 
            r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
    {
        let mut low: u32 = 0;
        let mut high: u32 = n;
        
        while low < high
            invariant
                low <= high &&
                low * low <= n &&
                (high > n || high * high > n)
            /* code modified by LLM (iteration 3): added decreases clause to prove termination */
            decreases high - low
        {
            let mid = low + (high - low) / 2;
            let mid_squared = mid * mid;
            
            if mid_squared <= n {
                if (mid + 1) * (mid + 1) > n {
                    return mid;
                }
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        low
    }

    fn main() {
        let test_val = 16u32;
        let result1 = mroot1(test_val);
        let result2 = mroot2(test_val);
        let result3 = mroot3(test_val);
        
        // Results are computed but not printed since print! is not supported in Verus
    }
}