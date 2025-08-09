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
            invariant 
                r >= 0,
                (r as int) * (r as int) <= n,
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
            invariant 
                r <= n,
                forall |k: int| r < k <= n ==> k * k > n,
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
        let mut high: u32 = n + 1;
        
        while low + 1 < high
            invariant 
                0 <= low < high,
                high <= n + 1,
                (low as int) * (low as int) <= n,
                (high as int) * (high as int) > n,
        {
            let mid = low + (high - low) / 2;
            if mid * mid <= n {
                low = mid;
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
        
        print_line("Testing square root implementations:");
        print_line("mroot1(16) = ");
        print_line("mroot2(16) = ");
        print_line("mroot3(16) = ");
    }
}