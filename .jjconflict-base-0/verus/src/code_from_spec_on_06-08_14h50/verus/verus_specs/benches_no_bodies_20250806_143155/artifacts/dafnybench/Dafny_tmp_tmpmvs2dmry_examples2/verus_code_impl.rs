use vstd::prelude::*;

verus! {
    // Addition by increment - working version
    fn add_by_inc(x: u32, y: u32) -> (z: u32)
        requires x as u64 + y as u64 <= u32::MAX as u64,
        ensures z as u64 == x as u64 + y as u64,
    {
        let mut result = x;
        let mut count = 0u32;
        
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        while count < y
            invariant 
                count <= y,
                result as u64 == x as u64 + count as u64,
                result as u64 + (y - count) as u64 <= u32::MAX as u64,
            decreases y - count,
        {
            result = result + 1;
            count = count + 1;
        }
        
        result
    }

    // Product function - multiplication by repeated addition
    fn product(m: u32, n: u32) -> (res: u32)
        requires m as u64 * n as u64 <= u32::MAX as u64,
        ensures res as u64 == m as u64 * n as u64,
    {
        let mut result = 0u32;
        let mut count = 0u32;
        
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        while count < n
            invariant 
                count <= n,
                result as u64 == m as u64 * count as u64,
                result as u64 + m as u64 * (n - count) as u64 <= u32::MAX as u64,
            decreases n - count,
        {
            result = add_by_inc(result, m);
            count = count + 1;
        }
        
        result
    }

    // GCD calculation function (Euclidean algorithm)
    fn gcd_calc(m: u32, n: u32) -> (res: u32)
        requires m > 0 && n > 0,
        ensures res > 0,
    {
        let mut a = m;
        let mut b = n;
        
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        while a != b
            invariant 
                a > 0,
                b > 0,
            decreases a + b,
        {
            if a > b {
                a = a - b;
            } else {
                b = b - a;
            }
        }
        
        a
    }

    // GCD specification function
    spec fn gcd(m: int, n: int) -> int
        recommends m > 0 && n > 0,
        decreases m + n,
    {
        if m == n {
            n
        } else if m > n {
            gcd(m - n, n)
        } else {
            gcd(m, n - m)
        }
    }

    fn main() {}
}