use vstd::prelude::*;

verus! {
    // Method 1: Linear search from 0 upward - Cost O(sqrt(n))
    fn mroot1(n: u32) -> (r: u32)
        requires n >= 0,
        ensures 
            r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Method 2: Linear search from n downward - Cost O(n)
    fn mroot2(n: u32) -> (r: u32)
        requires n >= 0,
        ensures 
            r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Method 3: Binary search - Cost O(log n)
    fn mroot3(n: u32) -> (r: u32)
        requires 
            n >= 0,
            n < 0xFFFF_FFFE,
        ensures 
            r >= 0 && (r as int) * (r as int) <= n < ((r + 1) as int) * ((r + 1) as int),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}